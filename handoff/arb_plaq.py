"""Ball-arithmetic seeds for the SU(2) plaquette ladder (gauge-invariant sector, spin-network basis).

Two kinds of certificate:
  truncated(J, n0, e, lam, beta):   the ladder with every link flux <= J (a finite model for each ring length).
      Z_{n0} is enclosed by a ball matrix exponential; Z_{2 n0} is bounded below by exp(-beta*theta) with theta an
      exactly evaluated Rayleigh quotient.
  untruncated(jstar, n0, e, lam, beta, c):   the full ladder. Z_{n0} is bounded above for every cutoff >= jstar by
      Tr exp(-beta (P H P - lam^2/c  P W Q W P)) + exp(beta (lam n0 + c)) * [S_all - S_{<= jstar}],
      S = sum over admissible labelings of exp(-beta e' sum_links j(j+1)), computed with a transfer matrix.
In both cases   eps_s <= 1 - exp(-beta theta) / Zup^2,   eps_t <= 1 - exp(-2 beta theta) / Zup^4,
and the two-purity recurrence (48 doublings, as in the CertifiedGaps core) turns the seeds into a bound for every
even ring length L >= n0.
"""
import itertools, json, sys, time
from fractions import Fraction as Fr
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from sympy import Rational
from flint import arb, arb_mat, fmpq, ctx
from su2_plaq import sn_basis, corner, tri
from arb_seed import certified_bound

ctx.prec = 160
aq = lambda f: arb(fmpq(int(f.numerator), int(f.denominator)))


def exact_ops(L, J2):
    """basis, diag4[i] = sum_links j2 (j2 + 2)  (= 4 sum j(j+1)), entries (row, col, k) of W = sum_p tr U_p / 2
    with amplitude amps[k] = (sign, exact rational square)."""
    q = J2 + 1
    basis = sn_basis(L, J2)
    pw = [q ** i for i in range(3 * L)]
    code = lambda st: sum(s * p for s, p in zip(st, pw))
    idx = {code(st): i for i, st in enumerate(basis)}
    amps, amp_id, tab = [], {}, {}

    def moves(key):
        if key in tab:
            return tab[key]
        b, t, r, rp, abp, atp, abn, atn = key
        out = []
        for db, drp, dt, dr in itertools.product((1, -1), repeat=4):
            bn, rpn, tn, rn = b + db, rp + drp, t + dt, r + dr
            if min(bn, rpn, tn, rn) < 0 or max(bn, rpn, tn, rn) > J2:
                continue
            sgn, sq = 1, Rational(1)
            for (a, jin, jout, jinn, joutn) in ((abp, r, b, rn, bn), (abn, b, rp, bn, rpn), (atn, rp, t, rpn, tn), (atp, t, r, tn, rn)):
                s, qq = corner(a, jin, jout, jinn, joutn)
                if s == 0:
                    sgn = 0; break
                sgn *= s; sq *= qq
            if sgn:
                val = (sgn, sq / 4)
                if val not in amp_id:
                    amp_id[val] = len(amps); amps.append(val)
                out.append(((db, dt, dr, drp), amp_id[val]))
        tab[key] = out
        return out

    rows, cols, ks = [], [], []
    for i, st in enumerate(basis):
        c0 = code(st)
        for x in range(L):
            y, z = (x + 1) % L, (x - 1) % L
            key = (st[3 * x], st[3 * x + 1], st[3 * x + 2], st[3 * y + 2], st[3 * z], st[3 * z + 1], st[3 * y], st[3 * y + 1])
            p0, p1, p2, p3 = pw[3 * x], pw[3 * x + 1], pw[3 * x + 2], pw[3 * y + 2]
            for (db, dt, dr, drp), k in moves(key):
                j = idx.get(c0 + db * p0 + dt * p1 + dr * p2 + drp * p3)
                if j is not None:
                    rows.append(j); cols.append(i); ks.append(k)
    diag4 = np.array([sum(j * (j + 2) for j in st) for st in basis], dtype=np.int64)
    return basis, diag4, np.array(rows), np.array(cols), np.array(ks), amps


def amp_arb(amps):
    return [arb(int(s)) * arb(fmpq(int(q.p), int(q.q))).sqrt() for s, q in amps]


def amp_float(amps):
    return np.array([s * float(q) ** 0.5 for s, q in amps])


def theta_upper(L, J2, e, lam, ops=None, bits=26):
    """Rigorous upper bound on the ground energy of the L-ring at any cutoff >= J2/2 (and of the full model):
    the Rayleigh quotient of an integer vector n, evaluated exactly.
        theta = [ (e/3) sum_i diag4_i n_i^2 - lam sum_k amp_k S_k ] / sum_i n_i^2 ,  S_k = sum_{entries of kind k} n_row n_col."""
    basis, diag4, rows, cols, ks, amps = ops or exact_ops(L, J2)
    n = len(basis)
    af = amp_float(amps)
    H = sp.csr_matrix((-float(lam) * af[ks], (rows, cols)), shape=(n, n)) + sp.diags(float(e) / 3 * diag4)
    if n <= 3000:
        w, V = np.linalg.eigh(H.toarray()); psi = V[:, 0]; e0 = w[0]
    else:
        w, V = eigsh(H.tocsr(), k=1, which="SA", tol=1e-13, ncv=40); psi = V[:, 0]; e0 = w[0]
    psi = psi / np.abs(psi).max()
    nint = np.rint(psi * 2 ** bits).astype(np.int64)                 # |n_i| <= 2^26, products < 2^52, chunks of 1024 < 2^62
    sq = nint * nint
    den = sum(int(x) for x in np.add.reduceat(sq, np.arange(0, n, 1024)))
    dsum = 0
    for v in np.unique(diag4):
        seg = sq[diag4 == v]
        dsum += int(v) * sum(int(x) for x in np.add.reduceat(seg, np.arange(0, len(seg), 1024)))
    prod = nint[rows] * nint[cols]
    order = np.argsort(ks, kind="stable"); ks_s, prod_s = ks[order], prod[order]
    S = [0] * len(amps)
    bounds = np.flatnonzero(np.diff(ks_s)) + 1
    starts = np.concatenate([[0], bounds]); ends = np.concatenate([bounds, [len(ks_s)]])
    for s0, s1 in zip(starts, ends):
        k = int(ks_s[s0]); seg = prod_s[s0:s1]
        S[k] = sum(int(x) for x in np.add.reduceat(seg, np.arange(0, len(seg), 1024)))
    aa = amp_arb(amps)
    num = aq(e) / 3 * arb(dsum) - aq(lam) * sum((aa[k] * arb(S[k]) for k in range(len(amps))), arb(0))
    theta = num / arb(den)
    return theta, float(e0)


def dense_arb(n, diag_entries, offdiag):
    M = arb_mat(n, n)
    for i, v in enumerate(diag_entries):
        M[i, i] = v
    for (r, c), v in offdiag.items():
        M[r, c] = M[r, c] + v
    return M


def trace_exp(M, n):
    E = M.exp()
    t = arb(0)
    for i in range(n):
        t += E[i, i]
    return t


def z_truncated(L, J2, e, lam, beta, ops=None):
    """Enclosure of Z_L(beta) for the ladder with cutoff J2/2."""
    basis, diag4, rows, cols, ks, amps = ops or exact_ops(L, J2)
    n = len(basis); aa = amp_arb(amps); b = aq(beta)
    off = {}
    for r, c, k in zip(rows.tolist(), cols.tolist(), ks.tolist()):
        off[(r, c)] = off.get((r, c), arb(0)) + b * aq(lam) * aa[k]            # -beta * (-lam W)
    M = dense_arb(n, [-(b * aq(e) / 3 * arb(int(d))) for d in diag4], off)
    return trace_exp(M, n)


def label_sum(L, J2, beta, e):
    """S_{<= J}(beta) = sum over admissible labelings with all spins <= J2/2 of exp(-beta e' sum j(j+1)), by transfer matrix."""
    b = aq(beta); ep = aq(e) * 4 / 3
    w = [(-(b * ep * arb(fmpq(j * (j + 2), 4)))).exp() for j in range(J2 + 1)]
    states = [(bb, tt) for bb in range(J2 + 1) for tt in range(J2 + 1)]
    n = len(states)
    T = arb_mat(n, n)
    for i, (b0, t0) in enumerate(states):
        for j, (b1, t1) in enumerate(states):
            s = arb(0)
            for r in range(J2 + 1):
                if tri(b0, b1, r) and tri(t0, t1, r):
                    s += w[r]
            T[i, j] = s * w[b1] * w[t1]
    P = T
    for _ in range(L - 1):
        P = P * T
    tr = arb(0)
    for i in range(n):
        tr += P[i, i]
    return tr, w


def tail_bound(L, jstar2, beta, e, lam, c, Jbig2=16):
    """exp(beta (lam L + c)) * [S_all - S_{<= jstar}], with S_all <= S_{<= Jbig} + remainder."""
    S_big, w = label_sum(L, Jbig2, beta, e)
    S_tr, _ = label_sum(L, jstar2, beta, e)
    b = aq(beta); ep = aq(e) * 4 / 3
    # remainder: labelings with some link above Jbig (constraints dropped). sum_{j2 > Jbig2} w(j2) <= w(Jbig2+1) / (1 - q),
    # q = w(Jbig2+2)/w(Jbig2+1) since the ratios decrease.
    w1 = (-(b * ep * arb(fmpq((Jbig2 + 1) * (Jbig2 + 3), 4)))).exp(); w2 = (-(b * ep * arb(fmpq((Jbig2 + 2) * (Jbig2 + 4), 4)))).exp()
    tail1 = w1 / (1 - w2 / w1)
    S1 = sum(w, arb(0)) + tail1
    rem = arb(3 * L) * tail1 * S1 ** (3 * L - 1)
    pref = (b * (aq(lam) * L + aq(c))).exp()
    return pref * (S_big - S_tr + rem), S_tr, S_big, rem


def z_upper_untruncated(L, jstar2, e, lam, beta, c):
    """Upper bound on Z_L(beta) valid for every cutoff >= jstar and for the full ladder."""
    basis, diag4, rows, cols, ks, amps = exact_ops(L, jstar2 + 1)
    aa = amp_arb(amps); b = aq(beta)
    inP = np.array([max(st) <= jstar2 for st in basis])
    pidx = -np.ones(len(basis), dtype=np.int64); pidx[inP] = np.arange(inP.sum()); nP = int(inP.sum())
    off = {}; byq = {}
    for r, cc, k in zip(rows.tolist(), cols.tolist(), ks.tolist()):
        if inP[r] and inP[cc]:
            key = (int(pidx[r]), int(pidx[cc])); off[key] = off.get(key, arb(0)) + b * aq(lam) * aa[k]
        elif (not inP[r]) and inP[cc]:
            byq.setdefault(r, []).append((int(pidx[cc]), aa[k]))
    coef = b * aq(lam) ** 2 / aq(c)                                # +beta lam^2/c K   (A = PHP - lam^2/c K)
    nk = 0
    for r, lst in byq.items():
        for (p1, a1) in lst:
            for (p2, a2) in lst:
                off[(p1, p2)] = off.get((p1, p2), arb(0)) + coef * a1 * a2; nk += 1
    diagP = diag4[inP]
    M = dense_arb(nP, [-(b * aq(e) / 3 * arb(int(d))) for d in diagP], off)
    main = trace_exp(M, nP)
    tail, S_tr, S_big, rem = tail_bound(L, jstar2, beta, e, lam, c)
    return main + tail, dict(dimP=nP, dim_big=len(basis), K_terms=nk, main=str(main), tail=str(tail), rem=str(rem))


def up(x):
    """Upper endpoint of a ball as a ball."""
    return arb(x.upper())


def seeds_and_bound(theta, Zup, beta):
    b = aq(beta)
    th = arb(theta.upper()); Z = arb(Zup.upper())
    es = 1 - (-(b * th)).exp() / Z ** 2
    et = 1 - (-(2 * b * th)).exp() / Z ** 4
    es_u, et_u = arb(es.upper()), arb(et.upper())
    bound = certified_bound(es_u, et_u, beta)
    return es_u, et_u, bound


def run_truncated(J2, n0, e, lam, beta, tag=None):
    t0 = time.time()
    ops_n = exact_ops(n0, J2); Z = z_truncated(n0, J2, e, lam, beta, ops_n); t1 = time.time()
    theta, e0f = theta_upper(2 * n0, J2, e, lam)
    es, et, bound = seeds_and_bound(theta, Z, beta)
    rec = dict(kind="truncated", J=J2 / 2, n0=n0, e=str(e), lam=str(lam), beta0=str(beta), dims=(len(ops_n[0]), None),
               Z_n0=str(Z), theta_2n0=str(theta), float_e0_2n0=e0f, eps_s=str(es), eps_t=str(et),
               bound=str(bound) if bound is not None else None,
               bound_lower=float(bound.lower()) if bound is not None else None, prec=ctx.prec,
               seconds=(round(t1 - t0, 1), round(time.time() - t1, 1)))
    print(json.dumps(rec), flush=True)
    return rec


def run_untruncated(jstar2, Jtrial2, n0, e, lam, beta, c):
    t0 = time.time()
    Zup, info = z_upper_untruncated(n0, jstar2, e, lam, beta, c); t1 = time.time()
    theta, e0f = theta_upper(2 * n0, Jtrial2, e, lam)
    es, et, bound = seeds_and_bound(theta, Zup, beta)
    rec = dict(kind="untruncated", jstar=jstar2 / 2, J_trial=Jtrial2 / 2, n0=n0, e=str(e), lam=str(lam), beta0=str(beta), c=str(c),
               Z_n0_upper=str(Zup), theta_2n0=str(theta), float_e0_2n0=e0f, eps_s=str(es), eps_t=str(et), **info,
               bound=str(bound) if bound is not None else None,
               bound_lower=float(bound.lower()) if bound is not None else None, prec=ctx.prec,
               seconds=(round(t1 - t0, 1), round(time.time() - t1, 1)))
    print(json.dumps(rec), flush=True)
    return rec


if __name__ == "__main__":
    mode = sys.argv[1]
    out_name = sys.argv[2]
    recs = []
    if mode == "trunc":      # args: J2 n0 e lam beta ...
        args = sys.argv[3:]
        for i in range(0, len(args), 5):
            J2, n0 = int(args[i]), int(args[i + 1]); e, lam, beta = Fr(args[i + 2]), Fr(args[i + 3]), Fr(args[i + 4])
            recs.append(run_truncated(J2, n0, e, lam, beta)); json.dump(recs, open(out_name, "w"), indent=1)
    else:                    # args: jstar2 Jtrial2 n0 e lam beta c ...
        args = sys.argv[3:]
        for i in range(0, len(args), 7):
            js, jt, n0 = int(args[i]), int(args[i + 1]), int(args[i + 2])
            e, lam, beta, c = Fr(args[i + 3]), Fr(args[i + 4]), Fr(args[i + 5]), Fr(args[i + 6])
            recs.append(run_untruncated(js, jt, n0, e, lam, beta, c)); json.dump(recs, open(out_name, "w"), indent=1)
