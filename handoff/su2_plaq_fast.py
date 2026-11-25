"""Faster builder for the spin-network ladder operators (float), with integer state codes and a local move table."""
import itertools, time
import numpy as np
import scipy.sparse as sp
from sympy import Rational
from su2_plaq import sn_basis, corner


def move_table(J2, exact=False):
    """key (b, t, r, rp, ab_prev, at_prev, ab_next, at_next) -> list of ((db, dt, dr, drp), amplitude of tr U_p / 2)."""
    tab = {}
    rng = range(J2 + 1)
    for key in itertools.product(rng, repeat=8):
        b, t, r, rp, abp, atp, abn, atn = key
        moves = []
        for db, drp, dt, dr in itertools.product((1, -1), repeat=4):
            bn, rpn, tn, rn = b + db, rp + drp, t + dt, r + dr
            if min(bn, rpn, tn, rn) < 0 or max(bn, rpn, tn, rn) > J2:
                continue
            sgn, sq = 1, Rational(1)
            for (a, jin, jout, jinn, joutn) in ((abp, r, b, rn, bn), (abn, b, rp, bn, rpn), (atn, rp, t, rpn, tn), (atp, t, r, tn, rn)):
                s, q = corner(a, jin, jout, jinn, joutn)
                if s == 0:
                    sgn = 0; break
                sgn *= s; sq *= q
            if sgn:
                moves.append(((db, dt, dr, drp), (sgn, sq / 4) if exact else sgn * float(sq) ** 0.5 / 2))
        if moves:
            tab[key] = moves
    return tab


def build(L, J2, exact=False, tab=None):
    """Returns (codes, diag, rows, cols, vals). diag = sum_links j(j+1) (float, or Rational if exact)."""
    q = J2 + 1
    basis = sn_basis(L, J2)
    pw = [q ** i for i in range(3 * L)]
    code = lambda st: sum(s * p for s, p in zip(st, pw))
    idx = {code(st): i for i, st in enumerate(basis)}
    tab = tab or move_table(J2, exact)
    rows, cols, vals = [], [], []
    for i, st in enumerate(basis):
        c0 = code(st)
        for x in range(L):
            y, z = (x + 1) % L, (x - 1) % L
            key = (st[3 * x], st[3 * x + 1], st[3 * x + 2], st[3 * y + 2], st[3 * z], st[3 * z + 1], st[3 * y], st[3 * y + 1])
            mv = tab.get(key)
            if not mv:
                continue
            p0, p1, p2, p3 = pw[3 * x], pw[3 * x + 1], pw[3 * x + 2], pw[3 * y + 2]
            for (db, dt, dr, drp), amp in mv:
                j = idx.get(c0 + db * p0 + dt * p1 + dr * p2 + drp * p3)
                if j is not None:
                    rows.append(j); cols.append(i); vals.append(amp)
    if exact:
        diag = [sum(Rational(j * (j + 2), 4) for j in st) for st in basis]
    else:
        diag = np.array([sum(j * (j + 2) for j in st) / 4.0 for st in basis])
    return basis, diag, rows, cols, vals


def float_ops(L, J2):
    basis, diag, rows, cols, vals = build(L, J2)
    n = len(basis)
    return diag, sp.csr_matrix((vals, (rows, cols)), shape=(n, n)), basis


if __name__ == "__main__":
    import sys
    from su2_plaq import sn_operators
    # consistency with the reference builder
    for L, J2 in ((2, 2), (4, 2), (3, 2)):
        d, W, b = float_ops(L, J2)
        b0, d0, r0, c0, v0 = sn_operators(L, J2)
        W0 = sp.csr_matrix((v0, (r0, c0)), shape=W.shape)
        print(L, J2, len(b), "max diff W:", abs(W - W0).max(), "diag:", np.abs(d - np.array([float(x) for x in d0])).max(), flush=True)
    t = time.time(); d, W, b = float_ops(8, 2); print("L=8 J=1:", len(b), W.nnz, round(time.time() - t, 1), "s", flush=True)
    sp.save_npz("W_L8_J1.npz", W); np.save("diag_L8_J1.npy", d)
