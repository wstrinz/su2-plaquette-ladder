"""Third construction of the ladder: a ring of L = 2 split-link cells assembled from the quadrature-built
cell of lemma1_cell_test.py (no 6j symbols), with a midpoint Gauss penalty. Its lowest levels must be the
spectrum of the spin-network (6j) Hamiltonian at the same flux cutoff, with multiplicities."""
import sys, json, numpy as np
from scipy.sparse.linalg import eigsh, LinearOperator
import su2_plaq
J2 = int(sys.argv[1]); e, lam, mu = 1.0, float(sys.argv[2]) if len(sys.argv) > 2 else 1.3, (40.0 if J2 == 1 else 10.0)
c = np.load(f"lemma1_cell_J{J2}.npz"); n = c["R"].shape[0]; ep = 4 * e / 3
site = (ep / 2 + mu) * c["Ch"] + ep * c["Cr"]            # electric energy of the half-links and rung, plus the diagonal part of the penalty
# bond between a left cell (first factor) and a right cell: penalty cross terms and the plaquette
# (G_b2 + G_b1')^2 = C_b2 + C_b1' + 2 G_b2.G_b1' and G.G' = -(iG)(iG)'
terms = [(-2 * mu * c["iGb2"][a], c["iGb1"][a]) for a in range(3)] + [(-2 * mu * c["iGt2"][a], c["iGt1"][a]) for a in range(3)]
terms += [(-lam * c["P"][k], c["Q"][k]) for k in range(4)]   # -(lam/2) tr(Q' P^dagger) = -lam sum_k P_k Q'_k
def matvec(v):
    Psi = v.reshape(n, n); out = site @ Psi + Psi @ site.T
    for A, B in terms:
        out += A @ Psi @ B.T          # bond (0 -> 1)
        out += B @ Psi @ A.T          # bond (1 -> 0): cell 1 is the left cell
    return out.ravel()
H = LinearOperator((n * n, n * n), matvec=matvec, dtype=float)
basis, Hs, W = su2_plaq.sn_hamiltonian(2, J2, e, lam); k = min(12 if J2 == 1 else 6, len(basis))
w = np.sort(eigsh(H, k=k, which="SA", tol=(1e-11 if J2 == 1 else 1e-8), ncv=(None if J2 == 1 else 40), return_eigenvectors=False))
ws = np.sort(np.linalg.eigvalsh(Hs.toarray()))[:k]
rep = dict(J=J2 / 2, lam=lam, cell_dim=int(n), ring_dim=int(n * n), spin_network_dim=len(basis), cell_ring=[round(float(x), 9) for x in w], spin_network=[round(float(x), 9) for x in ws],
           max_diff=float(np.abs(w - ws).max()))
print(json.dumps(rep)); json.dump(rep, open(f"cell_ring_check_J{J2}.json", "w"), indent=1)
