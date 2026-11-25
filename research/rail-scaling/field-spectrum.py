"""Compare finite-cutoff even and odd ground energies in a rail field."""
import argparse
from pathlib import Path
import sys

import numpy as np
from scipy.optimize import brentq
from scipy.sparse import coo_matrix, diags
from scipy.sparse.linalg import eigsh

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "handoff/zero_winding"))
from even_replay import even_ops


def sector(length, spin2, x, odd):
    basis, electric, rows, cols, ids, amps = even_ops(length, spin2, parity=odd)
    links = np.asarray(basis).reshape(-1, length, 3)
    signs = 1 - 2 * (links[:, :, :2] % 2)
    charge = (signs[:, :, 0] - signs[:, :, 1]).sum(axis=1) / 2
    if not odd:
        assert np.all(charge == 0)
    values = np.array([s * np.sqrt(float(square)) for s, square in amps])
    w = coo_matrix((values[ids], (rows, cols)), shape=(len(charge), len(charge))).tocsr()
    assert not (w - w.T).nnz
    h0 = diags(electric / 3) - x * w
    start = np.random.default_rng(541).normal(size=len(charge))
    def ground(h):
        matrix = h0 - diags(h * charge)
        eigen, vectors = eigsh(matrix, k=1, which="SA", tol=1e-12, v0=start)
        psi = vectors[:, 0]
        residual = np.linalg.norm(matrix @ psi - eigen[0] * psi)
        assert residual < 1e-8
        return eigen[0], (psi*psi) @ charge / length
    return ground


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("length", type=int)
    parser.add_argument("spin2", type=int, help="twice the largest allowed link spin")
    parser.add_argument("x", type=float)
    args = parser.parse_args()
    even, _ = sector(args.length, args.spin2, args.x, 0)(0)
    odd = sector(args.length, args.spin2, args.x, 1)
    hc = brentq(lambda h: odd(h)[0] - even, 0, 2 + args.x, xtol=1e-12)
    energy, m = odd(hc)
    assert abs(energy - even) < 1e-9
    print(f"L={args.length} 2J={args.spin2} x={args.x} h_c={hc:.9f} jump={m:.9f}")
