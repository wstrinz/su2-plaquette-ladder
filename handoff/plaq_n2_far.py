"""How far in lam do n0 = 2 seeds hold for the (converged) ladder? Z_2 at J = 5/2, E_0(4) at J = 2 (float)."""
import json, sys, time
import numpy as np, scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from su2_plaq_fast import float_ops
from su2_plaq_scan import best
from lib import logZ
t = time.time(); d2, W2, _ = float_ops(2, 5); d4, W4, b4 = float_ops(4, 4); d4b, W4b, _ = float_ops(4, 3)
print("dims", len(d2), len(d4), len(d4b), round(time.time() - t, 1), flush=True)
betas = np.concatenate([np.arange(0.5, 6, 0.125), np.arange(6, 12, 0.5)])
e = 1.0; out = []
for lam in (1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 8.0, 10.0):
    E2 = np.linalg.eigvalsh((sp.diags(4 * e / 3 * d2) - lam * W2).toarray())
    w4 = np.sort(eigsh((sp.diags(4 * e / 3 * d4) - lam * W4).tocsr(), k=4, which="SA", tol=1e-10, return_eigenvectors=False))
    w4b = float(eigsh((sp.diags(4 * e / 3 * d4b) - lam * W4b).tocsr(), k=1, which="SA", tol=1e-10, return_eigenvectors=False)[0])
    def seeds(b, th=w4[0]):
        lz = logZ(E2, b)
        return -np.expm1(-b * th - 2 * lz), -np.expm1(-2 * b * th - 4 * lz)
    bb = best(seeds, betas); bb15 = best(lambda b: seeds(b, w4b), betas)
    rec = dict(lam=lam, gap2=round(float(E2[1] - E2[0]), 5), gap4_J2=round(float(w4[1] - w4[0]), 5), e0_4_J2=round(float(w4[0]), 7), e0_4_J15=round(w4b, 7),
               n0_2_bound=bb, n0_2_bound_trialJ15=bb15)
    out.append(rec); print(json.dumps(rec), flush=True)
json.dump(out, open("plaq_n2_far.json", "w"), indent=1)
