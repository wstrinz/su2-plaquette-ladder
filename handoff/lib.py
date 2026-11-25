"""Recon library: purity-bootstrap seed defects and gap bounds for periodic chains.

Float/mpmath arithmetic only. Nothing here is a certificate; it reproduces the
criterion of the CertifiedGaps core (doubling map R, rates b_j, tail allowance)
so that candidate points can be scouted before any rigorous run.
"""
import itertools
import numpy as np
import scipy.sparse as sp
import mpmath as mp

mp.mp.dps = 60

# ---------------------------------------------------------------- recurrence


def zdef(a, b):
    """z(a,b) = 1-(1-b)(1-a)^2, written without cancellation."""
    return b + a * (2 - a) * (1 - b)


def fsq(z):
    return z * z / (2 * (1 - z) ** 2)


ZSTAR = 2 - mp.sqrt(2)
EPS_LOW = mp.mpf("0.12731")


def gap_bound(es, et, beta0, J=40):
    """Uniform gap bound b_J - tail from seed defects, or None if the criterion fails."""
    s, t = mp.mpf(es), mp.mpf(et)
    if s < -1e-9 or t < -1e-9:
        return None
    # float seeds carry ~1e-13 noise; R is order-preserving, so raising a defect to the floor is safe
    s, t = max(s, mp.mpf(10) ** -11), max(t, mp.mpf(10) ** -11)
    adm = False
    for j in range(J + 1):
        z = zdef(s, t)
        if z >= mp.mpf(1) / 2:
            return None
        if max(s, t) < EPS_LOW:
            adm = True
        if j == J:
            r = z / (1 - z)
            if not adm or r > mp.mpf(1) / 10:
                return None
            bJ = -mp.log(r) / (beta0 * mp.mpf(2) ** J)
            tail = mp.log(5) / (beta0 * mp.mpf(2) ** J)
            return float(bJ - tail)
        if z >= ZSTAR:
            return None
        s2 = fsq(z)
        z2 = zdef(t, s2)
        if z2 >= ZSTAR:
            return None
        s, t = s2, fsq(z2)


def doubling_step(es, et):
    z1 = zdef(es, et)
    s2 = fsq(z1)
    return s2, fsq(zdef(et, s2))


# ---------------------------------------------------------------- partition sums


def logZ(E, beta):
    E = np.asarray(E, dtype=float)
    e0 = E.min()
    return -beta * e0 + np.log(np.sum(np.exp(-beta * (E - e0))))


def seed_from_spectra(En, E2n, beta):
    """(eps_s, eps_t) at (n, beta) from full spectra of the n- and 2n-rings."""
    ln, l2, l22 = logZ(En, beta), logZ(E2n, beta), logZ(E2n, 2 * beta)
    return -np.expm1(l2 - 2 * ln), -np.expm1(l22 - 2 * l2)


def coupled_seed(En, E2n_low, beta):
    """Seed defects needing only a LOWER bound on Z_2n (partial list of Ritz values).

    eps_s <= 1 - Z_2n(b)^- / Z_n(b)^2,  eps_t <= 1 - Z_2n(2b)^- / Z_n(b)^4.
    """
    ln = logZ(En, beta)
    return -np.expm1(logZ(E2n_low, beta) - 2 * ln), -np.expm1(logZ(E2n_low, 2 * beta) - 4 * ln)


def best_bound(defect_fn, betas):
    """Scan beta; return (bound, beta, eps_s, eps_t) maximizing the bound."""
    best = (None, None, None, None)
    for b in betas:
        es, et = defect_fn(b)
        if not (np.isfinite(es) and np.isfinite(et)) or es >= 1 or et >= 0.5:
            continue
        g = gap_bound(es, et, b)
        if g is not None and (best[0] is None or g > best[0]):
            best = (g, b, es, et)
    return best


# ---------------------------------------------------------------- generic chain ED


def kron_site_ops(L, d, ops):
    """Sparse operator on (C^d)^{⊗L} with ops = {site: dxd matrix}."""
    out = sp.identity(1, format="csr")
    for j in range(L):
        out = sp.kron(out, sp.csr_matrix(ops[j]) if j in ops else sp.identity(d, format="csr"), format="csr")
    return out


def ring_hamiltonian(L, d, bond_pairs, onsite):
    """H_L = sum_j sum_k A_k(j) B_k(j+1) + sum_j onsite(j), periodic, both bonds kept at L=2."""
    H = sp.csr_matrix((d**L, d**L))
    for j in range(L):
        k = (j + 1) % L
        for A, B in bond_pairs:
            if j == k:
                H = H + kron_site_ops(L, d, {j: A @ B})
            else:
                H = H + kron_site_ops(L, d, {j: A, k: B})
        H = H + kron_site_ops(L, d, {j: onsite})
    return H


def spectrum(L, d, bond_pairs, onsite):
    H = ring_hamiltonian(L, d, bond_pairs, onsite).toarray()
    assert np.allclose(H, H.T.conj())
    return np.linalg.eigvalsh(H.real if np.isrealobj(H) or np.abs(H.imag).max() < 1e-14 else H)


# ---------------------------------------------------------------- finite groups


class Group:
    def __init__(self, name, elems, mul, char):
        self.name, self.elems = name, list(elems)
        self.n = len(self.elems)
        self.idx = {e: i for i, e in enumerate(self.elems)}
        self.mul = np.array([[self.idx[mul(a, b)] for b in self.elems] for a in self.elems])
        self.e = next(i for i in range(self.n) if all(self.mul[i, j] == j for j in range(self.n)))
        self.inv = np.array([next(j for j in range(self.n) if self.mul[i, j] == self.e) for i in range(self.n)])
        self.char = np.array([char(e) for e in self.elems], dtype=float)  # Re chi / chi(1)

    def R(self, h):  # R_h |w> = |w h>
        M = np.zeros((self.n, self.n))
        for w in range(self.n):
            M[self.mul[w, h], w] = 1
        return M

    def Lm(self, h):  # L_h |w> = |h^{-1} w>
        M = np.zeros((self.n, self.n))
        for w in range(self.n):
            M[self.mul[self.inv[h], w], w] = 1
        return M

    def F(self):  # inversion
        M = np.zeros((self.n, self.n))
        for w in range(self.n):
            M[self.inv[w], w] = 1
        return M

    def is_class_closed(self, S):
        S = set(S)
        return all(self.mul[self.mul[g, h], self.inv[g]] in S for g in range(self.n) for h in S) and all(
            self.inv[h] in S for h in S
        )


def cyclic(n):
    return Group(f"Z{n}", range(n), lambda a, b: (a + b) % n, lambda k: np.cos(2 * np.pi * k / n))


def s3():
    perms = list(itertools.permutations(range(3)))
    comp = lambda p, q: tuple(p[q[i]] for i in range(3))
    fixed = lambda p: sum(p[i] == i for i in range(3))
    return Group("S3", perms, comp, lambda p: (fixed(p) - 1) / 2.0)  # standard 2-dim rep


def q8():
    # unit quaternions ±1, ±i, ±j, ±k as integer 4-vectors
    def qmul(a, b):
        a1, b1, c1, d1 = a
        a2, b2, c2, d2 = b
        return (
            a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2,
            a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
            a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2,
            a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2,
        )

    els = []
    for i in range(4):
        for s in (1, -1):
            v = [0, 0, 0, 0]
            v[i] = s
            els.append(tuple(v))
    return Group("Q8", els, qmul, lambda q: float(q[0]))  # 2-dim rep: chi = 2*Re(q)


def gen_set(G):
    """Class-closed, inverse-closed generating set S used for the kinetic terms."""
    if G.name == "S3":
        S = [i for i, p in enumerate(G.elems) if sum(p[k] == k for k in range(3)) == 1]  # transpositions
    elif G.name == "Q8":
        S = [i for i, q in enumerate(G.elems) if q[0] == 0]  # ±i, ±j, ±k
    else:
        S = [i for i in range(G.n) if i != G.e]
    assert G.is_class_closed(S)
    return S


def gauge_higgs_chain(G, m, e, kappa):
    """Unitary-gauge 1+1D gauge-Higgs chain with gauge group G.

    H = -(m/|S|) sum_j sum_{h in S} R_h(j) L_h(j+1)      matter kinetic term
        -(e/|S|) sum_j sum_{h in S} L_h(j)               electric (link) term
        - kappa  sum_j Re chi(w_j)/chi(1)                hopping / Higgs term
    Returns (d, bond_pairs, onsite).
    """
    S = gen_set(G)
    pairs = [(-(m / len(S)) * G.R(h), G.Lm(h)) for h in S]
    onsite = -(e / len(S)) * sum(G.Lm(h) for h in S) - kappa * np.diag(G.char)
    return G.n, pairs, onsite


def rp_check(G, m, e, kappa):
    """Check the reflection-positive cell structure used by the CertifiedGaps core:
    -h_bond = sum_a C_a ⊗ F C_a F with real symmetric or antisymmetric C_a, F^2 = 1, F o F = o."""
    S = gen_set(G)
    F = G.F()
    d, pairs, o = gauge_higgs_chain(G, m, e, kappa)
    hb = sum(np.kron(A, B) for A, B in pairs)
    acc = np.zeros_like(hb)
    w = m / len(S)
    for h in S:
        Rh = G.R(h)
        for C in ((Rh + Rh.T) / 2, (Rh - Rh.T) / 2):
            acc += w * np.kron(C, F @ C @ F)
    ok_bond = np.allclose(-hb, acc)
    return (
        ok_bond
        and np.allclose(F @ F, np.eye(d))
        and np.allclose(F, F.T)
        and np.allclose(F @ o @ F, o)
        and np.allclose(o, o.T)
    )
