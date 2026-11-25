"""Float seeds at n0 = 4 for the SU(2) plaquette ladder truncated at J = 1: Z_4 exact, Z_8 from below."""
import json, sys, time
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from su2_plaq_fast import float_ops
from su2_plaq_scan import best
from lib import coupled_seed

d4, W4, _ = float_ops(4, 2)
d6, W6, _ = float_ops(6, 2)
W8 = sp.load_npz("W_L8_J1.npz"); d8 = np.load("diag_L8_J1.npy")
betas = np.concatenate([np.arange(0.5, 6, 0.25), np.arange(6, 16, 0.5), np.arange(16, 40, 2.0)])
out = []
for lam in [float(x) for x in sys.argv[1:]] or [0.5, 1.0, 2.0, 3.0]:
    e = 1.0; t0 = time.time()
    E4 = np.linalg.eigvalsh((sp.diags(4 * e / 3 * d4) - lam * W4).toarray())
    E6 = np.sort(eigsh((sp.diags(4 * e / 3 * d6) - lam * W6).tocsr(), k=12, which="SA", tol=1e-10, return_eigenvectors=False))
    E8 = np.sort(eigsh((sp.diags(4 * e / 3 * d8) - lam * W8).tocsr(), k=40, which="SA", tol=1e-10, ncv=120, return_eigenvectors=False))
    b = best(lambda bb: coupled_seed(E4, E8, bb), betas)
    rec = dict(e=e, lam=lam, J=1.0, gap4=round(float(E4[1] - E4[0]), 6), gap6=round(float(E6[1] - E6[0]), 6), gap8=round(float(E8[1] - E8[0]), 6),
               e0=[round(float(E4[0]), 8), round(float(E6[0]), 8), round(float(E8[0]), 8)],
               low8=[round(float(x - E8[0]), 4) for x in E8[:10]], n0_4=b, sec=round(time.time() - t0, 1))
    out.append(rec); print(json.dumps(rec), flush=True)
    json.dump(out, open("su2_plaq_n4.json", "w"), indent=1)
