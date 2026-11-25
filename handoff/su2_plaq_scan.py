"""Float exploration of the SU(2) plaquette ladder in the gauge-invariant (spin-network) basis:
gaps by ring length and cutoff, and purity-bootstrap seeds at n0 = 2 (and n0 = 4 with a lower bound on Z_8)."""
import json, sys, time
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from su2_plaq import sn_operators
from lib import gap_bound, logZ, seed_from_spectra, coupled_seed

_cache = {}


def ops(L, J2):
    if (L, J2) not in _cache:
        basis, diag, rows, cols, vals = sn_operators(L, J2)
        n = len(basis)
        _cache[(L, J2)] = (np.array([float(d) for d in diag]), sp.csr_matrix((vals, (rows, cols)), shape=(n, n)), basis)
    return _cache[(L, J2)]


def spec(L, J2, e, lam, k=None):
    d, W, _ = ops(L, J2)
    H = sp.diags(4 * e / 3 * d) - lam * W
    if k is None or H.shape[0] <= 3000:
        return np.linalg.eigvalsh(H.toarray())
    return np.sort(eigsh(H.tocsr(), k=k, which="SA", tol=1e-10, return_eigenvectors=False))


def best(defect, betas):
    out = None
    for b in betas:
        es, et = defect(b)
        if not (np.isfinite(es) and np.isfinite(et)) or es >= 1 or et >= 0.5 or es < -1e-9 or et < -1e-9:
            continue
        g = gap_bound(max(es, 1e-11), max(et, 1e-11), b)
        if g is not None and (out is None or g > out[0]):
            out = (float(g), float(b), float(es), float(et))
    return out


if __name__ == "__main__":
    betas = np.concatenate([np.arange(0.5, 6, 0.25), np.arange(6, 16, 0.5), np.arange(16, 40, 2.0)])
    res = []
    lams = [float(x) for x in sys.argv[1:]] or [0.25, 0.5, 0.8, 1.0, 1.5, 2.0, 3.0]
    for lam in lams:
        e = 1.0; t0 = time.time()
        E2 = {J2: spec(2, J2, e, lam) for J2 in (1, 2, 3, 4)}
        E4 = {J2: spec(4, J2, e, lam) for J2 in (1, 2)}
        E4[3] = spec(4, 3, e, lam, k=60)
        gaps = dict(L2={J2 / 2: round(float(E2[J2][1] - E2[J2][0]), 6) for J2 in E2},
                    L4={J2 / 2: round(float(E4[J2][1] - E4[J2][0]), 6) for J2 in E4},
                    e0_L2={J2 / 2: round(float(E2[J2][0]), 8) for J2 in E2}, e0_L4={J2 / 2: round(float(E4[J2][0]), 8) for J2 in E4})
        # n0 = 2: Z_2 from the largest cutoff, Z_4 lower bound from the partial J = 3/2 spectrum
        b2 = best(lambda b: coupled_seed(E2[4], E4[3], b), betas)
        b2_full = best(lambda b: seed_from_spectra(E2[2], E4[2], b), betas)      # same-cutoff J = 1 comparison
        rec = dict(e=e, lam=lam, **gaps, n0_2=b2, n0_2_J1_both=b2_full, sec=round(time.time() - t0, 1))
        res.append(rec); print(json.dumps(rec), flush=True)
        json.dump(res, open("su2_plaq_scan.json", "w"), indent=1)
