"""Certified gap bounds on whole coupling intervals for the untruncated SU(2) plaquette ladder (n0 = 2).

For lam in [la, lb] (e = 1), with t = (lam - la)/(lb - la):
  * E_0^{(4)}(lam) <= theta_a - (lam - la) w_a          (variational: the trial vector of la, w_a = <W>)
  * log Z_2(beta, lam) <= (1 - t) l_a + t l_b            (convexity of log Z in lam; l = log of the upper bound)
  * Z_4 <= Z_2^2                                         (purity at most one)
so  P_s(2, beta; lam) >= exp(-beta (theta_a - t d w_a) - 2 ((1-t) l_a + t l_b)),  d = lb - la,
    P_tau(4, beta; lam) >= exp(-2 beta (theta_a - t d w_a) - 4 ((1-t) l_a + t l_b)).
Both exponents are linear in t, so the worst case is at an endpoint. All bounds hold for every flux cutoff
>= max(jstar, J_trial), hence for the full ladder.

usage: arb_plaq_interval.py OUT.json jstar2 Jtrial2 c  la:lb:step:beta [la:lb:step:beta ...]
"""
import json, os, sys, time
from fractions import Fraction as Fr
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from flint import arb, arb_mat, fmpq, ctx
import arb_plaq as ap
from arb_plaq import aq, exact_ops, amp_arb, amp_float, dense_arb, trace_exp, tail_bound
from arb_seed import certified_bound

ctx.prec = 160
E = Fr(1)


class Zup:
    def __init__(self, jstar2, c):
        self.js, self.c = jstar2, c
        basis, diag4, rows, cols, ks, amps = exact_ops(2, jstar2 + 1)
        self.aa = amp_arb(amps)
        inP = np.array([max(st) <= jstar2 for st in basis]); pidx = -np.ones(len(basis), dtype=np.int64); pidx[inP] = np.arange(inP.sum())
        self.nP = int(inP.sum()); self.diagP = diag4[inP]
        self.pp = []; byq = {}
        for r, cc, k in zip(rows.tolist(), cols.tolist(), ks.tolist()):
            if inP[r] and inP[cc]:
                self.pp.append((int(pidx[r]), int(pidx[cc]), k))
            elif (not inP[r]) and inP[cc]:
                byq.setdefault(r, []).append((int(pidx[cc]), k))
        self.K = {}
        for r, lst in byq.items():
            for (p1, k1) in lst:
                for (p2, k2) in lst:
                    self.K[(p1, p2)] = self.K.get((p1, p2), arb(0)) + self.aa[k1] * self.aa[k2]
        self.tail_cache = {}

    def log_upper(self, beta, lam):
        """Upper endpoint of log of the upper bound on Z_2(beta, lam)."""
        b = aq(beta); l = aq(lam)
        off = {}
        for p1, p2, k in self.pp:
            off[(p1, p2)] = off.get((p1, p2), arb(0)) + b * l * self.aa[k]
        coef = b * l * l / aq(self.c)
        for key, v in self.K.items():
            off[key] = off.get(key, arb(0)) + coef * v
        M = dense_arb(self.nP, [-(b * aq(E) / 3 * arb(int(d))) for d in self.diagP], off)
        main = trace_exp(M, self.nP)
        tail = tail_bound(2, self.js, beta, E, lam, self.c)[0]
        z = main + tail
        return arb(z.log().upper()), float(tail.upper()) / float(main.mid())


class Trial:
    def __init__(self, J2, bits=26):
        self.basis, self.diag4, self.rows, self.cols, self.ks, self.amps = exact_ops(4, J2)
        self.n = len(self.basis); self.af = amp_float(self.amps); self.aa = amp_arb(self.amps); self.bits = bits
        self.Wf = sp.csr_matrix((self.af[self.ks], (self.rows, self.cols)), shape=(self.n, self.n))
        self.order = np.argsort(self.ks, kind="stable"); ks_s = self.ks[self.order]
        bounds = np.flatnonzero(np.diff(ks_s)) + 1
        self.starts = np.concatenate([[0], bounds]); self.ends = np.concatenate([bounds, [len(ks_s)]]); self.kval = ks_s[self.starts]
        self.v0 = None

    def theta_w(self, lam):
        """(upper bound on E_0^{(4)}(lam), lower bound on w = <W>, float E_0) for the integer trial vector at lam."""
        H = (sp.diags(float(E) / 3 * self.diag4) - float(lam) * self.Wf).tocsr()
        if lam == 0:                                     # exact vacuum: every link at spin 0
            psi = np.zeros(self.n); psi[int(np.argmin(self.diag4))] = 1.0; w = [0.0]
        else:
            w, V = eigsh(H, k=1, which="SA", tol=1e-13, ncv=40, v0=self.v0)
            psi = V[:, 0]; self.v0 = psi.copy()
        psi = psi / np.abs(psi).max()
        nint = np.rint(psi * 2 ** self.bits).astype(np.int64); sq = nint * nint; n = self.n
        den = sum(int(x) for x in np.add.reduceat(sq, np.arange(0, n, 1024)))
        dsum = 0
        for v in np.unique(self.diag4):
            seg = sq[self.diag4 == v]
            dsum += int(v) * sum(int(x) for x in np.add.reduceat(seg, np.arange(0, len(seg), 1024)))
        prod = (nint[self.rows] * nint[self.cols])[self.order]
        wsum = arb(0)
        for s0, s1, k in zip(self.starts, self.ends, self.kval):
            seg = prod[s0:s1]
            wsum += self.aa[int(k)] * arb(sum(int(x) for x in np.add.reduceat(seg, np.arange(0, len(seg), 1024))))
        wexp = wsum / arb(den)
        theta = aq(E) / 3 * arb(dsum) / arb(den) - aq(lam) * wexp
        return arb(theta.upper()), arb(wexp.lower()), float(w[0])


def interval_bound(beta, d, th_a, w_a, l_a, l_b):
    b = aq(beta)
    x0s = -(b * th_a) - 2 * l_a; x1s = -(b * (th_a - aq(d) * w_a)) - 2 * l_b
    x0t = -(2 * b * th_a) - 4 * l_a; x1t = -(2 * b * (th_a - aq(d) * w_a)) - 4 * l_b
    es = arb(max((1 - x0s.exp()).upper(), (1 - x1s.exp()).upper()))
    et = arb(max((1 - x0t.exp()).upper(), (1 - x1t.exp()).upper()))
    if not (es > 0) or not (et > 0):
        return es, et, None
    return es, et, certified_bound(es, et, beta)


if __name__ == "__main__":
    out_name = sys.argv[1]; js, jt = int(sys.argv[2]), int(sys.argv[3]); c = Fr(sys.argv[4])
    recs = json.load(open(out_name)) if os.path.exists(out_name) else []
    done = {(r["la"], r["lb"]) for r in recs}
    t0 = time.time(); Z = Zup(js, c); T = Trial(jt)
    print(f"setup {time.time() - t0:.1f}s  P-dim {Z.nP}  K entries {len(Z.K)}  trial dim {T.n}", flush=True)
    budget = float(os.environ.get("BUDGET", "520"))
    for seg in sys.argv[5:]:
        la0, lb0, step, beta = (Fr(x) for x in seg.split(":"))
        pts = []
        x = la0
        while x < lb0:
            pts.append(x); x += step
        pts.append(lb0)
        lcache = {}
        for a, bnd in zip(pts[:-1], pts[1:]):
            if (str(a), str(bnd)) in done:
                continue
            if time.time() - t0 > budget:
                print("budget reached", flush=True); json.dump(recs, open(out_name, "w"), indent=1); sys.exit(0)
            t1 = time.time()
            for lam in (a, bnd):
                if lam not in lcache:
                    lcache[lam] = Z.log_upper(beta, lam)
            th_a, w_a, e0f = T.theta_w(a)
            es, et, bound = interval_bound(beta, bnd - a, th_a, w_a, lcache[a][0], lcache[bnd][0])
            rec = dict(la=str(a), lb=str(bnd), beta0=str(beta), jstar=js / 2, J_trial=jt / 2, c=str(c),
                       theta_a=float(th_a.mid()), w_a=float(w_a.mid()), float_e0=e0f, logZup_a=float(lcache[a][0].mid()), logZup_b=float(lcache[bnd][0].mid()),
                       tail_rel_b=lcache[bnd][1], eps_s=float(es.upper()), eps_t=float(et.upper()),
                       bound_lower=float(bound.lower()) if bound is not None else None, sec=round(time.time() - t1, 1))
            recs.append(rec); done.add((str(a), str(bnd)))
            print(json.dumps(rec), flush=True)
            json.dump(recs, open(out_name, "w"), indent=1)
    print("done", round(time.time() - t0, 1), flush=True)
