"""Float emulation of the untruncated n0 = 4 certificate, to choose (beta0, c) and see what truncation error costs."""
import sys, json
import numpy as np, scipy.sparse as sp
from su2_plaq_fast import float_ops
from su2_plaq import tri
from lib import gap_bound

e = 1.0
lam = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0
d, W, basis = float_ops(4, 3)
inP = np.array([max(st) <= 2 for st in basis]); P = np.flatnonzero(inP); Q = np.flatnonzero(~inP)
Wc = W.tocsr(); WQP = Wc[Q][:, P]; K = (WQP.T @ WQP).toarray(); HPP = (sp.diags(4 * e / 3 * d) - lam * W).tocsr()[P][:, P].toarray()
W8 = sp.load_npz("W_L8_J1.npz"); d8 = np.load("diag_L8_J1.npy")
from scipy.sparse.linalg import eigsh
theta8 = float(eigsh((sp.diags(4 * e / 3 * d8) - lam * W8).tocsr(), k=1, which="SA", tol=1e-12, return_eigenvectors=False)[0])
print("theta8 (J=1 trial):", theta8, " E_Q,min electric:", 4 * e / 3 * d[Q].min(), flush=True)

def label_sum(L, J2, beta):
    w = np.exp(-beta * 4 * e / 3 * np.array([j * (j + 2) / 4 for j in range(J2 + 1)]))
    st = [(b, t) for b in range(J2 + 1) for t in range(J2 + 1)]
    T = np.array([[sum(w[r] for r in range(J2 + 1) if tri(b0, b1, r) and tri(t0, t1, r)) * w[b1] * w[t1] for (b1, t1) in st] for (b0, t0) in st])
    return np.trace(np.linalg.matrix_power(T, L))

best = None
for c in (6.0, 7.0, 8.0, 9.0, 10.0):
    A = np.linalg.eigvalsh(HPP - lam ** 2 / c * K)
    for beta in np.arange(2.0, 3.51, 0.125):
        tail = np.exp(beta * (lam * 4 + c)) * (label_sum(4, 14, beta) - label_sum(4, 2, beta))
        Zup = np.exp(-beta * A).sum() + tail
        es = 1 - np.exp(-beta * theta8) / Zup ** 2; et = 1 - np.exp(-2 * beta * theta8) / Zup ** 4
        g = gap_bound(es, et, beta) if 0 < es < 0.3 and 0 < et < 0.4 else None
        if g is not None and (best is None or g > best[0]):
            best = (float(g), c, float(beta), float(es), float(et), float(tail))
    print("c =", c, "best so far:", best, flush=True)
