"""Float check of the truncation inequality for the 2-plaquette ring: how close is Zup(jstar, c) to the converged Z_2?"""
import numpy as np, scipy.sparse as sp, mpmath as mp
from su2_plaq_fast import float_ops
from su2_plaq import tri
e = 1.0
def label_sum(L, J2, beta):
    w = [mp.e ** (-beta * 4 * e / 3 * j * (j + 2) / 4) for j in range(J2 + 1)]
    st = [(b, t) for b in range(J2 + 1) for t in range(J2 + 1)]
    T = mp.matrix(len(st), len(st))
    for i, (b0, t0) in enumerate(st):
        for j, (b1, t1) in enumerate(st):
            T[i, j] = sum(w[r] for r in range(J2 + 1) if tri(b0, b1, r) and tri(t0, t1, r)) * w[b1] * w[t1]
    P = T
    for _ in range(L - 1): P = P * T
    return sum(P[i, i] for i in range(len(st)))
mp.mp.dps = 40
dref, Wref, _ = float_ops(2, 5)
ops = {js: float_ops(2, js + 1) for js in (3, 4)}
for lam, beta in ((1.0, 5.0), (2.0, 4.125), (3.0, 3.75), (4.0, 3.75), (5.0, 3.75)):
    Eref = np.linalg.eigvalsh((sp.diags(4 * e / 3 * dref) - lam * Wref).toarray()); lzref = np.log(np.exp(-beta * (Eref - Eref[0])).sum()) - beta * Eref[0]
    line = f"lam={lam} beta={beta} logZ_ref(J=5/2)={lzref:.8f} |"
    for js in (3, 4):
        d, W, basis = ops[js]
        inP = np.array([max(st) <= js for st in basis]); P = np.flatnonzero(inP); Q = np.flatnonzero(~inP)
        Wc = W.tocsr(); K = (Wc[Q][:, P].T @ Wc[Q][:, P]).toarray(); HPP = (sp.diags(4 * e / 3 * d) - lam * W).tocsr()[P][:, P].toarray()
        eq = 4 * e / 3 * d[Q].min()
        bestc = None
        for c in (1, 2, 3, 4, 6, 8, 10, 12):
            A = np.linalg.eigvalsh(HPP - lam ** 2 / c * K)
            tail = float(mp.e ** (beta * (2 * lam + c)) * (label_sum(2, 8, beta) - label_sum(2, js, beta)))
            lz = np.log(np.exp(-beta * (A - A[0])).sum() * np.exp(-beta * A[0]) + tail)
            if bestc is None or lz < bestc[1]: bestc = (c, lz, tail)
        line += f" jstar={js/2}: best c={bestc[0]} logZup-logZref={bestc[1]-lzref:.2e} tail={bestc[2]:.1e} EQmin={eq:.1f} |"
    print(line, flush=True)
