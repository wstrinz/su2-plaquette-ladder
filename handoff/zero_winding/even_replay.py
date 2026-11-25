"""even_replay.py -- second implementation for the zero-winding theorem: replays the seed inequalities of the
Lean files LadderEven/Part1..Part4 for every interval, independently of the Julia code that produced the seeds.

For each interval [la, lb] with inverse temperature beta and seeds s0, t0 read from the Lean file, it proves that for
every coupling in the interval and every flux cutoff >= the ones used
        1 - s0 <= exp(-beta E0(4) - 2 log Zup(2)),        1 - t0 <= exp(-2 beta E0(4) - 4 log Zup(2)),
where everything is restricted to the sector c = +1 of the winding charge c = (-1)^(2 j_b + 2 j_t).

What differs from the Julia implementation (zero_winding/even_seeds.jl, replay/ladder_replay.jl):
  language            Python
  6j symbols          sympy (through su2_plaq.corner), not Racah's sum
  basis, operators    built here, sector-restricted from the start
  Tr exp (Lemma 3)    EXACT integer arithmetic: with V an integer matrix (rounded float eigenvectors times 2^52) and the
                      operator written as an integer matrix plus a bounded remainder, V^T M V and V^T V are computed with
                      FLINT integer matrix products; then Gershgorin row sums and Courant-Fischer (see trace_exp_upper)
  scalars             Arb balls, 128 bits
  label sums          ball transfer matrix over the pairs (j_b, j_t) with j_b + j_t integer
  trial vectors       26-bit integer vectors from scipy's Lanczos, Rayleigh quotient evaluated exactly per amplitude class
What is shared: the mathematics (Lemmas 3, 4, 5 and the cited corner formula) and the author.

usage: even_replay.py compute tiling.json OUT.jsonl first last        (stage 1: defect bounds, no seeds read)
       even_replay.py check LEAN1,LEAN2,... RESULT.json OUT.jsonl [OUT2.jsonl ...]   (stage 2: compare with the Lean seeds)
"""
import array, json, math, re, sys, time, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from fractions import Fraction as Fr
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from flint import arb, arb_mat, fmpq, fmpz_mat, ctx
from su2_plaq import corner, tri          # corner factor from sympy's wigner_6j

ctx.prec = 128
aq = lambda f: arb(fmpq(int(Fr(f).numerator), int(Fr(f).denominator)))
SV = 52            # eigenvector scale: V = V_int / 2^SV (float eigenvectors times 2^52 are exact integers)
SM = 64            # operator scale: amplitudes are rounded to multiples of 2^-SM
JBIG2 = 16


# ----------------------------------------------------------------------------- basis and operators (sector c = +1)

def even_basis(L, J2, parity=0):
    """Admissible labelings (b_0, t_0, r_0, ..., b_{L-1}, t_{L-1}, r_{L-1}) with doubled spins <= J2 and b_0 + t_0 of the
    given parity (0: sector c = +1, the default; 1: sector c = -1)."""
    out = []; vals = range(J2 + 1)

    def rec(x, st):
        if x == L:
            if tri(st[3 * L - 3], st[0], st[2]) and tri(st[3 * L - 2], st[1], st[2]):
                out.append(tuple(st))
            return
        for b in vals:
            for t in vals:
                if x == 0 and (b + t) % 2 != parity:
                    continue
                for r in vals:
                    if x > 0 and not (tri(st[3 * x - 3], b, r) and tri(st[3 * x - 2], t, r)):
                        continue
                    rec(x + 1, st + [b, t, r])
    rec(0, [])
    return out


_corner = {}
def corner_fr(a, jin, jout, jinn, joutn):
    key = (a, jin, jout, jinn, joutn)
    v = _corner.get(key)
    if v is None:
        s, q = corner(a, jin, jout, jinn, joutn)
        v = _corner[key] = (int(s), Fr(int(q.p), int(q.q)) if s else Fr(0))
    return v


def even_ops(L, J2, parity=0):
    """basis, diag4 (= 4 sum j(j+1), integers), entries (rows, cols, ks) of W = sum_p tr U_p / 2 inside the sector,
    amps[k] = (sign, exact square)."""
    basis = even_basis(L, J2, parity); q = J2 + 1
    pw = [q ** i for i in range(3 * L)]
    code = lambda st: sum(s * p for s, p in zip(st, pw))
    idx = {code(st): i for i, st in enumerate(basis)}
    amps, amp_id, tab = [], {}, {}
    rows, cols, ks = array.array("i"), array.array("i"), array.array("i")
    for i, st in enumerate(basis):
        c0 = code(st)
        for x in range(L):
            y, z = (x + 1) % L, (x - 1) % L
            key = (st[3 * x], st[3 * x + 1], st[3 * x + 2], st[3 * y + 2], st[3 * z], st[3 * z + 1], st[3 * y], st[3 * y + 1])
            mv = tab.get(key)
            if mv is None:
                b, t, r, rp, abp, atp, abn, atn = key; mv = []
                for db in (1, -1):
                    for dt in (1, -1):
                        for dr in (1, -1):
                            for drp in (1, -1):
                                bn, tn, rn, rpn = b + db, t + dt, r + dr, rp + drp
                                if min(bn, tn, rn, rpn) < 0 or max(bn, tn, rn, rpn) > J2:
                                    continue
                                sgn, sq = 1, Fr(1)
                                for (a, jin, jout, jinn, joutn) in ((abp, r, b, rn, bn), (abn, b, rp, bn, rpn), (atn, rp, t, rpn, tn), (atp, t, r, tn, rn)):
                                    s, qq = corner_fr(a, jin, jout, jinn, joutn)
                                    if s == 0:
                                        sgn = 0; break
                                    sgn *= s; sq *= qq
                                if sgn:
                                    val = (sgn, sq / 4)
                                    k = amp_id.get(val)
                                    if k is None:
                                        k = amp_id[val] = len(amps); amps.append(val)
                                    mv.append(((db, dt, dr, drp), k))
                tab[key] = mv
            p0, p1, p2, p3 = pw[3 * x], pw[3 * x + 1], pw[3 * x + 2], pw[3 * y + 2]
            for (db, dt, dr, drp), k in mv:
                j = idx.get(c0 + db * p0 + dt * p1 + dr * p2 + drp * p3)
                if j is not None:
                    rows.append(j); cols.append(i); ks.append(k)
    diag4 = np.array([sum(j * (j + 2) for j in st) for st in basis], dtype=np.int64)
    return basis, diag4, np.frombuffer(rows, dtype=np.int32), np.frombuffer(cols, dtype=np.int32), np.frombuffer(ks, dtype=np.int32), amps


def amp_arb(amps):
    return [arb(int(s)) * aq(q).sqrt() for s, q in amps]


def dyadic(x, S):
    """Integer m with |x - m / 2^S| <= rad(x) + 2^-S, for an Arb ball x (exact arithmetic on the midpoint)."""
    man, ex = x.mid().man_exp(); man, ex = int(man), int(ex)
    sh = ex + S
    return man << sh if sh >= 0 else man >> (-sh)        # floor: error < 2^-S


# ----------------------------------------------------------------------------- Lemma 3 in the sector

class ZUp:
    """Upper bounds on log Z+(2, beta) valid for every cutoff >= js2 / 2."""

    def __init__(self, js2, c, parity=0):
        self.js2, self.c, self.parity = js2, Fr(c), parity
        basis, diag4, rows, cols, ks, amps = even_ops(2, js2 + 1, parity)
        # smallest diag4 among sector labelings with some label above js2 (used by ground_lower): labelings whose largest
        # label is js2 + 1 are enumerated; if the largest label m is >= js2 + 2, the two other links at one end of that
        # link have labels a, b with a + b >= m (triangle rule), so diag4 >= m(m+2) + min over a + b >= m of a(a+2) + b(b+2).
        d1 = min(int(d) for st, d in zip(basis, diag4) if max(st) == js2 + 1)
        m = js2 + 2
        d2 = m * (m + 2) + min(a * (a + 2) + (m - a) * (m - a + 2) for a in range(m + 1))
        self.dmin = min(d1, d2)
        aa = amp_arb(amps)
        inP = np.array([max(st) <= js2 for st in basis]); pidx = -np.ones(len(basis), dtype=np.int64); pidx[inP] = np.arange(inP.sum())
        n = self.n = int(inP.sum()); self.diagP = [int(d) for d in diag4[inP]]
        W = {}; byq = {}
        for r, cc, k in zip(rows.tolist(), cols.tolist(), ks.tolist()):
            if not inP[cc]:
                continue
            if inP[r]:
                key = (int(pidx[r]), int(pidx[cc])); W[key] = W.get(key, arb(0)) + aa[k]
            else:
                byq.setdefault(r, []).append((int(pidx[cc]), k))
        K = {}
        for lst in byq.values():
            for p1, k1 in lst:
                for p2, k2 in lst:
                    K[(p1, p2)] = K.get((p1, p2), arb(0)) + aa[k1] * aa[k2]
        # integer versions: X = X_int / 2^SM + remainder, |remainder| <= rX entrywise
        def pack(d):
            M = [0] * (n * n); rmax = 0.0; F = np.zeros((n, n))
            for (i, j), v in d.items():
                M[i * n + j] = dyadic(v, SM); F[i, j] = float(v.mid())
                rmax = max(rmax, float(v.rad().upper()) * (1 + 1e-12) + 1e-300)        # generous upper bound on the radius
            return fmpz_mat(n, n, M), arb((arb(rmax) + arb(2) ** (-SM)).upper()), F
        self.Wi, self.rW, self.Wf = pack(W)
        self.Ki, self.rK, self.Kf = pack(K)
        self.Di = fmpz_mat(n, n, [self.diagP[i] if i == j else 0 for i in range(n) for j in range(n)])
        self.cache = {}

    def trace_exp_upper(self, beta, lam):
        """Upper bound on Tr exp(M), M = -(beta/3) D + beta lam W + (beta lam^2 / c) K, all on the sector part of P.

        Write beta = pb/qb, lam = pl/ql, c = pc/qc and Q = 3 qb ql^2 pc. Then Q 2^SM M = Mi + Q 2^SM Delta with the
        integer matrix   Mi = -(pb ql^2 pc 2^SM) D + (3 pb pl ql pc) Wi + (3 pb pl^2 qc) Ki
        and |Delta| <= rho := beta lam rW + (beta lam^2 / c) rK entrywise. With V = Vi / 2^SV:
            V^T M V = Vi^T Mi Vi / (Q 2^(SM + 2 SV)) + V^T Delta V,   |V^T Delta V|_ik <= rho S_i S_k,  S_i = sum_a |V_ai|,
            G = V^T V = Vi^T Vi / 2^(2 SV)                       (exact).
        If eta >= ||G - I||_2 (Frobenius norm here) is < 1, V is invertible, and with u_i = A_ii + sum_{k != i} |A_ik|
        (A = V^T M V, enclosed as above) the k-th largest eigenvalue of M is at most u_(k)/(1 - eta) if u_(k) >= 0 and
        u_(k)/(1 + eta) otherwise (diag(u) - A is diagonally dominant; Courant-Fischer with y = V x). Hence
            Tr exp(M) <= sum_i exp(that bound for u_i)."""
        n = self.n; b, l, c = Fr(beta), Fr(lam), self.c
        pb, qb, pl, ql, pc, qc = b.numerator, b.denominator, l.numerator, l.denominator, c.numerator, c.denominator
        Q = 3 * qb * ql * ql * pc
        assert Fr(-pb * ql * ql * pc, Q) == -b / 3 and Fr(3 * pb * pl * ql * pc, Q) == b * l and Fr(3 * pb * pl * pl * qc, Q) == b * l * l / c
        Mi = self.Di * (-((pb * ql * ql * pc) << SM)) + self.Wi * (3 * pb * pl * ql * pc) + self.Ki * (3 * pb * pl * pl * qc)
        Mf = -float(b) / 3 * np.diag(np.array(self.diagP, dtype=float)) + float(b * l) * self.Wf + float(b * l * l / c) * self.Kf
        Mf = (Mf + Mf.T) / 2
        V = np.linalg.eigh(Mf)[1]
        Vint = np.rint(V * 2.0 ** SV).astype(np.int64)
        Vi = fmpz_mat(n, n, Vint.ravel().tolist())
        Vt = Vi.transpose()
        A = [int(x) for x in (Vt * (Mi * Vi)).entries()]
        G = [int(x) for x in (Vt * Vi).entries()]
        one = 1 << (2 * SV); fro2 = 0
        for i in range(n):
            row = G[i * n:(i + 1) * n]
            fro2 += sum(x * x for x in row) - row[i] * row[i] + (row[i] - one) ** 2
        eta = arb((arb(fro2).sqrt() / arb(one)).upper())
        assert eta < arb(1) / 4, "eigenvector matrix too far from orthogonal"
        S = [sum(int(x) for x in col) for col in np.abs(Vint).T.tolist()]            # column sums of |Vi|, exact Python integers
        Stot = sum(S)
        rho = aq(b * l) * self.rW + aq(b * l * l / c) * self.rK
        scaleA = arb(Q) * arb(2) ** (SM + 2 * SV); sv2 = arb(2) ** (2 * SV)
        tot = arb(0); umax = None
        for i in range(n):
            row = A[i * n:(i + 1) * n]
            col_i = A[i::n]                                    # the integer matrix need not be exactly symmetric: use the larger of the two
            gers = sum(max(abs(x), abs(y)) for x, y in zip(row, col_i)) - max(abs(row[i]), abs(col_i[i]))
            u = (arb(row[i]) + arb(gers)) / scaleA + rho * arb(S[i]) * arb(Stot) / sv2
            u = arb(u.upper())
            ut = u / (1 - eta) if u >= 0 else (u / (1 + eta) if u < 0 else arb(max((u / (1 - eta)).upper(), (u / (1 + eta)).upper())))
            tot += arb(ut.upper()).exp()
            if umax is None or ut.upper() > umax:
                umax = arb(ut.upper())
        self.last_umax = umax                       # upper bound on the largest eigenvalue of M
        return arb(tot.upper())

    def ground_lower(self, lam):
        """Lower bound on the lowest eigenvalue of H on 2 plaquettes in this sector, for every cutoff >= js2 / 2:
        H >= A (+) B (proof of Lemma 3), so E0 >= min(lambda_min(A), dmin / 3 - (2 lam + c))."""
        self.trace_exp_upper(Fr(1), lam)             # M = -A at beta = 1
        a = -self.last_umax
        bmin = arb(self.dmin) / 3 - (2 * aq(lam) + aq(self.c))
        return arb(min(a.lower(), bmin.lower()))

    def label_sum(self, J2, beta):
        """Sum over sector labelings on 2 plaquettes with all doubled spins <= J2 of exp(-beta diag4 / 3) (e = 1)."""
        b = aq(beta)
        w = [(-(b / 3 * (j * (j + 2)))).exp() for j in range(J2 + 1)]
        states = [(bb, tt) for bb in range(J2 + 1) for tt in range(J2 + 1) if (bb + tt) % 2 == self.parity]
        n = len(states); T = arb_mat(n, n)
        for i, (b0, t0) in enumerate(states):
            for j, (b1, t1) in enumerate(states):
                s = arb(0)
                for r in range(J2 + 1):
                    if tri(b0, b1, r) and tri(t0, t1, r):
                        s += w[r]
                T[i, j] = s * w[b1] * w[t1]
        P = T * T; tr = arb(0)
        for i in range(n):
            tr += P[i, i]
        return tr, w

    def tail(self, beta, lam):
        """exp(beta (lam L + c)) [S_all - S_{<= jstar}] in the sector, L = 2; S_all <= S_{<= 8} + 3L tau S1^(3L-1) (constraints dropped)."""
        if beta not in self.cache:
            old = ctx.prec; ctx.prec = 8192          # S_all - S_{<= jstar} is a difference of nearly equal numbers (at beta = 20 it is below 1e-370 of either)
            S_big, w = self.label_sum(JBIG2, beta); S_tr, _ = self.label_sum(self.js2, beta)
            b = aq(beta)
            w1 = (-(b / 3 * ((JBIG2 + 1) * (JBIG2 + 3)))).exp(); w2 = (-(b / 3 * ((JBIG2 + 2) * (JBIG2 + 4)))).exp()
            tau = w1 / (1 - w2 / w1)
            S1 = sum(w, arb(0)) + tau
            diff = S_big - S_tr + 6 * tau * S1 ** 5
            assert diff > 0
            ctx.prec = old
            self.cache[beta] = arb(diff.upper())
        return (aq(beta) * (aq(lam) * 2 + aq(self.c))).exp() * self.cache[beta]

    def log_upper(self, beta, lam):
        main = self.trace_exp_upper(beta, lam); tail = self.tail(beta, lam)
        assert tail >= 0
        z = main + tail
        return arb(z.log().upper()), float(tail.upper()) / float(main.mid())


# ----------------------------------------------------------------------------- Lemma 4: trial vector on 4 plaquettes

class Trial:
    def __init__(self, J2, bits=26, L=4, parity=0):
        self.basis, self.diag4, self.rows, self.cols, self.ks, amps = even_ops(L, J2, parity)
        self.n = len(self.basis); self.bits = bits
        self.aa = amp_arb(amps); af = np.array([s * float(q) ** 0.5 for s, q in amps])
        self.Wf = sp.csr_matrix((af[self.ks], (self.rows, self.cols)), shape=(self.n, self.n))
        self.order = np.argsort(self.ks, kind="stable"); ks_s = self.ks[self.order]
        bounds = np.flatnonzero(np.diff(ks_s)) + 1
        self.starts = np.concatenate([[0], bounds]); self.ends = np.concatenate([bounds, [len(ks_s)]]); self.kval = ks_s[self.starts]
        self.v0 = None

    def theta_w(self, la, lam_vec):
        """(upper bound on E0+(4) at la, lower bound on <W>) for the integer vector obtained at coupling lam_vec."""
        H = (sp.diags(self.diag4 / 3.0) - float(lam_vec) * self.Wf).tocsr()
        if lam_vec == 0:
            psi = np.zeros(self.n); psi[int(np.argmin(self.diag4))] = 1.0
        else:
            w, V = eigsh(H, k=1, which="SA", tol=1e-12, ncv=40, v0=self.v0)
            psi = V[:, 0]; self.v0 = psi.copy()
        psi = psi / np.abs(psi).max()
        nint = np.rint(psi * 2 ** self.bits).astype(np.int64); sq = nint * nint; n = self.n
        chunks = lambda a: sum(int(x) for x in np.add.reduceat(a, np.arange(0, len(a), 1024))) if len(a) else 0     # |n_i| <= 2^26: no overflow
        den = chunks(sq); dsum = 0
        for v in np.unique(self.diag4):
            dsum += int(v) * chunks(sq[self.diag4 == v])
        prod = (nint[self.rows] * nint[self.cols])[self.order]
        wsum = arb(0)
        for s0, s1, k in zip(self.starts, self.ends, self.kval):
            wsum += self.aa[int(k)] * arb(chunks(prod[s0:s1]))
        wexp = wsum / arb(den)
        theta = arb(dsum) / (3 * arb(den)) - aq(la) * wexp
        return arb(theta.upper()), arb(wexp.lower())


# ----------------------------------------------------------------------------- the Lean file

def parse_dec(s):
    m = re.fullmatch(r"(\d+)(?:\.(\d+))?(?:e(-?\d+))?", s.strip()); frac = m.group(2) or ""
    return Fr(int(m.group(1) + frac)) * Fr(10) ** (int(m.group(3) or 0) - len(frac))


def read_lean(paths):
    """Intervals (la, lb, beta, s0, t0) from one or more Lean files (comma-separated), in file order."""
    out = []
    for line in (l for path in paths.split(",") for l in open(path, encoding="utf-8")):
        m = re.match(r"\s*⟨([^,]+),([^,]+),([^,]+),\s*\{\s*s := \[([^\]]*)\],\s*t := \[([^\]]*)\],", line)
        if m:
            f = lambda s: Fr(s.replace(" ", ""))
            out.append(dict(la=f(m.group(1)), lb=f(m.group(2)), beta=f(m.group(3)), s0=parse_dec(m.group(4).split(",")[0]), t0=parse_dec(m.group(5).split(",")[0])))
    return out


def compute(tilingf, outp, first, last):
    """Stage 1: for each interval of the tiling, rigorous upper bounds on the two seed defects (no seeds are read)."""
    til = json.load(open(tilingf)); last = min(last, len(til))
    done = set()
    if os.path.exists(outp):
        done = {json.loads(l)["i"] for l in open(outp)}
    zc, tc, lc = {}, {}, {}; t00 = time.time(); fh = open(outp, "a")
    for i in range(first, last + 1):
        if i in done:
            continue
        cf = til[i - 1]; t0 = time.time()
        la, lb, beta, c, js2, jt2 = Fr(cf["la"]), Fr(cf["lb"]), Fr(cf["beta"]), Fr(cf["c"]), cf["js2"], cf["jt2"]
        if (js2, c) not in zc:
            zc[(js2, c)] = ZUp(js2, c); print(f"L=2 sector operators at j* = {js2}/2: P-dim {zc[(js2, c)].n}", flush=True)
        if jt2 not in tc:
            tc[jt2] = Trial(jt2); print(f"L=4 sector operators at cutoff {jt2}/2: dim {tc[jt2].n}, entries {len(tc[jt2].rows)}", flush=True)
        Z, T = zc[(js2, c)], tc[jt2]
        for lam in (la, lb):
            if (js2, beta, lam) not in lc:
                lc[(js2, beta, lam)] = Z.log_upper(beta, lam)
        l_a, l_b = lc[(js2, beta, la)][0], lc[(js2, beta, lb)][0]
        th, w = T.theta_w(la, (la + lb) / 2)
        b = aq(beta); d = aq(lb - la)
        x0s = -(b * th) - 2 * l_a; x1s = -(b * (th - d * w)) - 2 * l_b
        x0t = -(2 * b * th) - 4 * l_a; x1t = -(2 * b * (th - d * w)) - 4 * l_b
        upf = lambda x: math.nextafter(float(x.upper()), math.inf)             # a float that is certainly >= the ball
        es = max(upf(1 - x0s.exp()), upf(1 - x1s.exp())); et = max(upf(1 - x0t.exp()), upf(1 - x1t.exp()))
        fh.write(json.dumps(dict(i=i, la=cf["la"], lb=cf["lb"], beta=cf["beta"], js2=js2, jt2=jt2, c=cf["c"], eps_s_up=es, eps_t_up=et,
                                 theta=float(th.mid()), w=float(w.mid()), logZup_a=float(l_a.mid()), logZup_b=float(l_b.mid()), tail_rel_b=lc[(js2, beta, lb)][1])) + "\n"); fh.flush()
        print(f"{i:3d} [{la}, {lb}] beta {beta}  eps_s <= {es:.9g}  eps_t <= {et:.9g}  ({time.time() - t0:.1f}s)", flush=True)
        if len(lc) > 8:
            lc.pop(next(iter(lc)))
    print(f"done {first}..{last}, {time.time() - t00:.0f}s", flush=True)


def check(lean, outp, files):
    """Stage 2: every interval of the Lean file must be covered by a computed row with the same beta whose defect bounds
    are at most the seeds s0, t0 of the Lean file (exact rational comparison)."""
    ivs = read_lean(lean)
    assert ivs[0]["la"] == 0 and all(a["lb"] == b["la"] for a, b in zip(ivs, ivs[1:]))
    rows = {}
    for f in files:
        for l in open(f):
            r = json.loads(l)
            r.setdefault("eps_s_up", r.get("eps_s")); r.setdefault("eps_t_up", r.get("eps_t"))     # rows of even_seeds.jl use these names
            rows[(Fr(r["la"]), Fr(r["lb"]))] = r
    res = []; npass = 0
    for i, iv in enumerate(ivs, 1):
        r = rows.get((iv["la"], iv["lb"]))
        ok = r is not None and Fr(r["beta"]) == iv["beta"] and Fr(r["eps_s_up"]) <= iv["s0"] and Fr(r["eps_t_up"]) <= iv["t0"]
        npass += ok
        res.append(dict(i=i, la=str(iv["la"]), lb=str(iv["lb"]), beta=str(iv["beta"]), s0=float(iv["s0"]), t0=float(iv["t0"]), ok=bool(ok),
                        eps_s_replay=None if r is None else r["eps_s_up"], eps_t_replay=None if r is None else r["eps_t_up"],
                        rel_slack_s=None if r is None else (float(iv["s0"]) - r["eps_s_up"]) / r["eps_s_up"],
                        rel_slack_t=None if r is None else (float(iv["t0"]) - r["eps_t_up"]) / r["eps_t_up"]))
    sl = [min(x["rel_slack_s"], x["rel_slack_t"]) for x in res if x["rel_slack_s"] is not None]
    summary = dict(intervals=len(ivs), last_coupling=str(ivs[-1]["lb"]), passed=npass, worst_rel_slack=min(sl) if sl else None)
    json.dump(dict(summary=summary, rows=res), open(outp, "w"))
    print(summary)
    for x in res:
        if not x["ok"]:
            print("FAIL", x)


if __name__ == "__main__":
    if sys.argv[1] == "compute":
        compute(sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]))
    else:
        check(sys.argv[2], sys.argv[3], sys.argv[4:])
