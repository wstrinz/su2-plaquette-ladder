"""Constructed-matrix test of split-link positivity (Lemma 1) for SU(2) at flux cutoff J.

Independent of su2_plaq.py: no 6j symbols, no fitted reflection. The cell is L^2(SU(2)^3) in the
invariants X = b'b'', Y = t't'', Z = b' r t''. Every single-variable operator is computed by exact
quadrature on the binary icosahedral group (120 points, a spherical 11-design on S^3), from the
definitions as operators on functions. The cutoff space V_J is the joint spectral subspace of the five
link Casimirs. Then the statements of the lemma are checked as matrix identities.
Usage: python3 lemma1_cell_test.py 1      (twice the cutoff: 1 -> J = 1/2, 2 -> J = 1)"""
import sys, itertools, math, json
import numpy as np
from scipy.linalg import logm
J2 = int(sys.argv[1]) if len(sys.argv) > 1 else 1
sig = [np.eye(2), np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]), np.array([[1, 0], [0, -1]], complex)]
q2m = lambda q: q[0] * sig[0] + 1j * (q[1] * sig[1] + q[2] * sig[2] + q[3] * sig[3])

def binary_icosahedral():
    phi = (1 + 5 ** .5) / 2; pts = set()
    for i in range(4):
        for s in (1, -1):
            v = [0.] * 4; v[i] = s; pts.add(tuple(v))
    for s in itertools.product((.5, -.5), repeat=4): pts.add(s)
    even = [p for p in itertools.permutations(range(4)) if sum(p[i] > p[j] for i in range(4) for j in range(i + 1, 4)) % 2 == 0]
    for p in even:
        for s in itertools.product((1, -1), repeat=3):
            base = [s[0] * phi / 2, s[1] * .5, s[2] / (2 * phi), 0.]
            pts.add(tuple(round(base[p.index(i)], 12) for i in range(4)))
    P = np.array(sorted(pts)); assert len(P) == 120 and np.allclose((P ** 2).sum(1), 1)
    return [q2m(q) for q in P]

def wigner(j2, g):
    """Spin j = j2/2 matrix of g on homogeneous polynomials of degree j2 in (u, v); a unitary representation."""
    n = j2 + 1; D = np.zeros((n, n), complex); a, b, c, d = g[0, 0], g[0, 1], g[1, 0], g[1, 1]
    norm = lambda k: math.sqrt(math.factorial(k) * math.factorial(j2 - k))        # basis u^k v^(j2-k) / norm(k)
    for k in range(n):                                                          # image of u^k v^(j2-k) under (u, v) -> (a u + c v, b u + d v)
        pa = np.poly1d([a, c]) ** k * np.poly1d([b, d]) ** (j2 - k)             # polynomial in u with v = 1
        co = pa.coeffs[::-1] if pa.order == j2 else np.concatenate([pa.coeffs[::-1], np.zeros(j2 - pa.order)])
        for l in range(n): D[l, k] = co[l] * norm(l) / norm(k)
    return D

G = binary_icosahedral()
spins = list(range(J2 + 1))                                    # twice the spins 0 .. J
idx = [(j2, m, n) for j2 in spins for m in range(j2 + 1) for n in range(j2 + 1)]; d1 = len(idx)
def evalb(g):                                                  # orthonormal basis sqrt(2j+1) D^j_{mn}(g)
    out = np.empty(d1, complex); p = 0
    for j2 in spins:
        D = wigner(j2, g) * math.sqrt(j2 + 1); out[p:p + D.size] = D.ravel(); p += D.size
    return out
Eg = np.array([evalb(g) for g in G])                           # 120 x d1
quad = lambda F: Eg.conj().T @ F / 120                         # <e_i, f_j> for columns f_j given on the grid
gram = quad(Eg); assert np.allclose(gram, np.eye(d1), atol=1e-12), "quadrature / orthonormality fails"
inv = lambda g: g.conj().T
Einv = np.array([evalb(inv(g)) for g in G])
Iop = quad(Einv)                                               # inversion (I f)(g) = f(g^-1)
Mg = [[quad(Eg * np.array([g[a, b] for g in G])[:, None]) for b in range(2)] for a in range(2)]        # multiply by g_ab
Mgi = [[quad(Eg * np.array([inv(g)[a, b] for g in G])[:, None]) for b in range(2)] for a in range(2)]  # multiply by (g^-1)_ab
Kmat = quad(Eg.conj())                                         # conj(e_j) = sum_k Kmat[k, j] e_k
eps = 0.37
def gens():
    SL, SR = [], []
    for a in (1, 2, 3):
        h = np.cos(eps / 2) * sig[0] - 1j * np.sin(eps / 2) * sig[a]              # exp(-i eps sigma_a / 2)
        Lh = quad(np.array([evalb(inv(h) @ g) for g in G])); Rh = quad(np.array([evalb(g @ h) for g in G]))
        SL.append(1j * logm(Lh) / eps); SR.append(1j * logm(Rh) / eps)
    return SL, SR
SL, SR = gens()
for S in SL + SR: assert np.allclose(S, S.conj().T, atol=1e-10)
# I M[D^c_us]: the single-variable pieces of the reflection
IM = {}
for c2 in spins:
    Dc = np.array([wigner(c2, inv(g)) for g in G])
    for u in range(c2 + 1):
        for s_ in range(c2 + 1): IM[(c2, u, s_)] = quad(Einv * Dc[:, u, s_][:, None])
one = np.eye(d1); k3 = lambda A, B, C: np.kron(np.kron(A, B), C)
N = d1 ** 3
# reflection (refl psi)(X, Y, Z) = psi(X^-1, Y^-1, X^-1 Z Y^-1), compressed to the box
refl = np.zeros((N, N), complex); zpos = {t: i for i, t in enumerate(idx)}
for c2 in spins:
    for u, v, s_, w in itertools.product(range(c2 + 1), repeat=4):
        Zop = np.zeros((d1, d1)); Zop[zpos[(c2, s_, w)], zpos[(c2, u, v)]] = 1
        refl += k3(IM[(c2, u, s_)], IM[(c2, w, v)], Zop)
Gb1 = [k3(SL[a], one, one) + k3(one, one, SL[a]) for a in range(3)]; Gb2 = [k3(SR[a], one, one) for a in range(3)]
Gt1 = [k3(one, SL[a], one) for a in range(3)]; Gt2 = [k3(one, SR[a], one) + k3(one, one, SR[a]) for a in range(3)]
cas = lambda Gs: sum(g @ g for g in Gs)
Cb1, Cb2, Ct1, Ct2 = cas(Gb1), cas(Gb2), cas(Gt1), cas(Gt2); Cr = cas([k3(one, one, SL[a]) for a in range(3)])
# cutoff space: all five Casimirs <= J(J+1)   (Cb2, Ct1, Cr hold on the whole box)
cap = (J2 / 2) * (J2 / 2 + 1) + 1e-6
def proj_le(C):
    w, U = np.linalg.eigh((C + C.conj().T) / 2); U = U[:, w <= cap]; return U @ U.conj().T
P12 = proj_le(Cb1) @ proj_le(Ct2); w, U = np.linalg.eigh((P12 + P12.conj().T) / 2); V = U[:, w > 0.5]; n = V.shape[1]
comp = lambda A: V.conj().T @ A @ V
rep = {"J": J2 / 2, "box_dim": N, "V_dim": n}
rep["casimirs_commute"] = float(np.abs(Cb1 @ Ct2 - Ct2 @ Cb1).max())
R = comp(refl)
rep["refl_unitary_on_V"] = float(np.abs(R.conj().T @ R - np.eye(n)).max()); rep["refl_involution"] = float(np.abs(R @ R - np.eye(n)).max())
rep["refl_hermitian"] = float(np.abs(R - R.conj().T).max())
rep["refl_swaps_generators"] = float(max(np.abs(R @ comp(Gb2[a]) @ R - comp(Gb1[a])).max() + np.abs(R @ comp(Gt2[a]) @ R - comp(Gt1[a])).max() for a in range(3)))
rep["wrong_generator_pairing"] = float(min(np.abs(R @ comp(Gb2[a]) @ R + comp(Gb1[a])).max() for a in range(3)))      # must be O(1)
e1, mu1 = 1.3, 0.7
o = comp((e1 / 2 + mu1) * (Cb1 + Cb2 + Ct1 + Ct2) + e1 * Cr)
rep["refl_commutes_with_o"] = float(np.abs(R @ o @ R - o).max())
# open lines P = X^-1 Z and Q = Z Y^-1 as matrix-valued multiplication operators, then quaternion components
Pab = [[sum(k3(Mgi[a][c], one, Mg[c][b]) for c in range(2)) for b in range(2)] for a in range(2)]
Qab = [[sum(k3(one, Mgi[c][b], Mg[a][c]) for c in range(2)) for b in range(2)] for a in range(2)]
def quatc(Mab):   # components of M = m0 + i m.sigma:  m0 = tr M / 2, m_k = tr(M sigma_k) / (2i)
    return [comp(sum(Mab[a][b] * sig[k][b, a] for a in range(2) for b in range(2)) / (2 if k == 0 else 2j)) for k in range(4)]
Pm, Qm = quatc(Pab), quatc(Qab)
rep["line_components_hermitian"] = float(max(np.abs(A - A.conj().T).max() for A in Pm + Qm))
rep["refl_maps_P_to_Q"] = float(max(np.abs(R @ Pm[k] @ R - Qm[k]).max() for k in range(4)))
rep["wrong_line_pairing"] = float(max(np.abs(R @ Pm[k] @ R + Qm[k]).max() for k in (1, 2, 3)))                      # must be O(1)
# real structure: K v = U conj(v) with U = Kmat^(x3); real basis of V
Ubig = k3(Kmat, Kmat, Kmat); KV = Ubig @ V.conj()
rep["V_invariant_under_conjugation"] = float(np.abs(KV - V @ (V.conj().T @ KV)).max())
T = V.conj().T @ KV                                           # K on coordinates: c -> T conj(c), T symmetric unitary
wT, UT = np.linalg.eigh((T + T.conj().T) / 2 + 0.618 * ((T - T.conj().T) / 2j))   # generic real combination to split
# real vectors: c with T conj(c) = c.  Build by symmetrising a random basis and orthonormalising with the real inner product.
rng = np.random.default_rng(1); Cz = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
Cr_ = Cz + T @ Cz.conj(); Qr, _ = np.linalg.qr(np.vstack([Cr_.real, Cr_.imag])); B = Qr[:n] + 1j * Qr[n:]
B = B[:, :n]; gramB = B.conj().T @ B
rep["real_basis_orthonormal"] = float(np.abs(gramB - np.eye(n)).max()); rep["real_basis_fixed"] = float(np.abs(T @ B.conj() - B).max())
tr = lambda A: B.conj().T @ A @ B
ops_sym = {"o": o, "refl": R, **{f"P{k}": Pm[k] for k in range(4)}, **{f"Q{k}": Qm[k] for k in range(4)}}
ops_anti = {f"iG{nm}{a}": 1j * comp(Gs[a]) for nm, Gs in (("b1", Gb1), ("b2", Gb2), ("t1", Gt1), ("t2", Gt2)) for a in range(3)}
rep["real_symmetric_ops_imag"] = float(max(np.abs(tr(A).imag).max() for A in ops_sym.values()))
rep["real_symmetric_ops_asym"] = float(max(np.abs(tr(A) - tr(A).T).max() for A in ops_sym.values()))
rep["real_antisymmetric_ops_imag"] = float(max(np.abs(tr(A).imag).max() for A in ops_anti.values()))
rep["real_antisymmetric_ops_sym"] = float(max(np.abs(tr(A) + tr(A).T).max() for A in ops_anti.values()))
print(json.dumps({k: (float("%.2e" % v) if isinstance(v, float) else v) for k, v in rep.items()}, indent=1))
json.dump(rep, open(f"lemma1_cell_test_J{J2}.json", "w"), indent=1)
# save the cell in the real basis, for the independent ring model (cell_ring_check.py)
np.savez(f"lemma1_cell_J{J2}.npz", Ch=tr(comp(Cb1 + Cb2 + Ct1 + Ct2)).real, Cr=tr(comp(Cr)).real, R=tr(R).real,
         iGb1=np.array([tr(1j * comp(g)).real for g in Gb1]), iGb2=np.array([tr(1j * comp(g)).real for g in Gb2]),
         iGt1=np.array([tr(1j * comp(g)).real for g in Gt1]), iGt2=np.array([tr(1j * comp(g)).real for g in Gt2]),
         P=np.array([tr(A).real for A in Pm]), Q=np.array([tr(A).real for A in Qm]),
         Cb1=tr(comp(Cb1)).real, Cb2=tr(comp(Cb2)).real, Ct1=tr(comp(Ct1)).real, Ct2=tr(comp(Ct2)).real)
