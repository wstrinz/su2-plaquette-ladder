"""SU(2) Kogut-Susskind plaquette ladder, two independent constructions.

(A) Spin-network basis (gauge-invariant sector only). A periodic ladder of L plaquettes has links
    b_x, t_x (legs) and r_x (rungs); a basis state assigns a spin to every link, with the triangle rule at
    every (trivalent) vertex. The plaquette operator tr U_p shifts its four links by +-1/2 with an amplitude
    that is a product of four 6j symbols (one per corner).
        H = e' sum_links j(j+1) - (lam/2) sum_p tr U_p ,   e' = 4e/3.

(B) Group side: the split-link cell model of ladder_fg.py for G = SU(2) in the Peter-Weyl basis, cell
    variables (B, T, P), with a Gauss penalty at the link midpoints. Its penalty-free levels must coincide
    with the spectrum of (A) at the same flux cutoff. Nothing in (B) uses 6j symbols.
"""
import itertools, json, sys, time
from functools import lru_cache
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh, LinearOperator
from sympy import Rational
from sympy.physics.wigner import wigner_6j

# ----------------------------------------------------------------------------- (A) spin networks


@lru_cache(maxsize=None)
def sixj_sq_sign(a2, b2, c2, d2, e2, f2):
    """6j symbol {a b c; d e f} with doubled arguments, returned as (sign, exact rational square)."""
    v = wigner_6j(Rational(a2, 2), Rational(b2, 2), Rational(c2, 2), Rational(d2, 2), Rational(e2, 2), Rational(f2, 2))
    if v == 0:
        return 0, Rational(0)
    return (1 if v > 0 else -1), (v * v)


@lru_cache(maxsize=None)
def corner(a2, jin2, jout2, jin2n, jout2n):
    """Corner factor: external leg a, loop links (in, out) changing to (in', out').
    F = (-1)^(a + j_out + 1/2 + j_in') sqrt((2 j_in + 1)(2 j_out' + 1)) {a j_out j_in; 1/2 j_in' j_out'}.
    Returned as (sign, exact rational square)."""
    try:
        s, q = sixj_sq_sign(a2, jout2, jin2, 1, jin2n, jout2n)
    except ValueError:
        return 0, Rational(0)
    if s == 0:
        return 0, Rational(0)
    ph = (a2 + jout2 + 1 + jin2n) // 2
    return (s * (-1) ** ph), q * (jin2 + 1) * (jout2n + 1)


def tri(a, b, c):
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b


def sn_basis(L, J2):
    """All labelings (b_0, t_0, r_0, ..., b_{L-1}, t_{L-1}, r_{L-1}) in half-units, spins <= J2/2.
    Vertex (x, bottom): (b_{x-1}, b_x, r_x); vertex (x, top): (t_{x-1}, t_x, r_x)."""
    vals = range(J2 + 1)
    out = []

    def rec(x, st):
        if x == L:
            b0, t0, r0 = st[0], st[1], st[2]
            bl, tl = st[3 * (L - 1)], st[3 * (L - 1) + 1]
            if tri(bl, b0, r0) and tri(tl, t0, r0):
                out.append(tuple(st))
            return
        for b in vals:
            for t in vals:
                for r in vals:
                    if x > 0 and not (tri(st[3 * (x - 1)], b, r) and tri(st[3 * (x - 1) + 1], t, r)):
                        continue
                    rec(x + 1, st + [b, t, r])

    rec(0, [])
    return out


def plaquette_moves(st, x, L, J2):
    """Yield (new_state, sign, exact_square) for tr U_p on plaquette x (between rungs x and x+1)."""
    y, z = (x + 1) % L, (x - 1) % L
    b, t, r, rp = st[3 * x], st[3 * x + 1], st[3 * x + 2], st[3 * y + 2]
    ab_next, at_next, ab_prev, at_prev = st[3 * y], st[3 * y + 1], st[3 * z], st[3 * z + 1]
    for db, drp, dt, dr in itertools.product((1, -1), repeat=4):
        bn, rpn, tn, rn = b + db, rp + drp, t + dt, r + dr
        if min(bn, rpn, tn, rn) < 0 or max(bn, rpn, tn, rn) > J2:
            continue
        if L == 2:
            # with two plaquettes the external legs of p_x are the legs of the other plaquette (unchanged)
            pass
        sgn, sq = 1, Rational(1)
        for (a, jin, jout, jinn, joutn) in ((ab_prev, r, b, rn, bn), (ab_next, b, rp, bn, rpn),
                                            (at_next, rp, t, rpn, tn), (at_prev, t, r, tn, rn)):
            s, q = corner(a, jin, jout, jinn, joutn)
            if s == 0:
                sgn = 0; break
            sgn *= s; sq *= q
        if sgn == 0:
            continue
        new = list(st); new[3 * x], new[3 * x + 1], new[3 * x + 2], new[3 * y + 2] = bn, tn, rn, rpn
        yield tuple(new), sgn, sq


def sn_operators(L, J2, exact=False):
    """Electric diagonal (in units where one link of spin j contributes j(j+1)) and W = sum_p tr U_p / 2,
    as (basis, diag, rows, cols, vals). With exact=True the values are (sign, rational square) pairs."""
    basis = sn_basis(L, J2); idx = {s: i for i, s in enumerate(basis)}
    diag = [sum(Rational(j * (j + 2), 4) for j in st) for st in basis]
    rows, cols, vals = [], [], []
    for i, st in enumerate(basis):
        for x in range(L):
            for new, sgn, sq in plaquette_moves(st, x, L, J2):
                j = idx.get(new)
                if j is None:
                    continue
                rows.append(j); cols.append(i)
                vals.append((sgn, sq / 4) if exact else sgn * float(sq) ** 0.5 / 2)
    return basis, diag, rows, cols, vals


def sn_hamiltonian(L, J2, e, lam):
    basis, diag, rows, cols, vals = sn_operators(L, J2)
    n = len(basis)
    W = sp.csr_matrix((vals, (rows, cols)), shape=(n, n))
    H = sp.diags([4 * e / 3 * float(d) for d in diag]) - lam * W
    return basis, H.tocsr(), W

# ----------------------------------------------------------------------------- (B) group side


def pw_single(J2):
    """One SU(2) variable, orthonormal basis e^j_{mn} = sqrt(2j+1) D^j_{mn}(w), j <= J2/2.
    Returns Casimir, generators SL[a], SR[a] (a = x, y, z) and the multiplication operators M[(a,b)] by D^{1/2}_{ab}."""
    B = [(j2, m2, n2) for j2 in range(J2 + 1) for m2 in range(-j2, j2 + 1, 2) for n2 in range(-j2, j2 + 1, 2)]
    idx = {b: i for i, b in enumerate(B)}; d = len(B)

    def cg(j2, m2, a2, jp2):   # <j m; 1/2 a | j' m+a>
        j, m = j2 / 2, m2 / 2
        if jp2 == j2 + 1:
            return np.sqrt((j + (a2 * m) + 1) / (2 * j + 1))
        if jp2 == j2 - 1:
            return (-a2) * np.sqrt((j - a2 * m) / (2 * j + 1)) if j2 > 0 else 0.0
        return 0.0

    C = np.zeros((d, d)); Jz_m = np.zeros((d, d)); Jz_n = np.zeros((d, d)); Jp_m = np.zeros((d, d)); Jp_n = np.zeros((d, d))
    M = {(a, b): np.zeros((d, d)) for a in (1, -1) for b in (1, -1)}
    for (j2, m2, n2), i in idx.items():
        j, m, n = j2 / 2, m2 / 2, n2 / 2
        C[i, i] = j * (j + 1); Jz_m[i, i] = m; Jz_n[i, i] = n
        if m2 + 2 <= j2: Jp_m[idx[(j2, m2 + 2, n2)], i] = np.sqrt(j * (j + 1) - m * (m + 1))
        if n2 + 2 <= j2: Jp_n[idx[(j2, m2, n2 + 2)], i] = np.sqrt(j * (j + 1) - n * (n + 1))
        for a in (1, -1):
            for b in (1, -1):
                for jp2 in (j2 + 1, j2 - 1):
                    if jp2 < 0 or jp2 > J2 or abs(m2 + a) > jp2 or abs(n2 + b) > jp2:
                        continue
                    M[(a, b)][idx[(jp2, m2 + a, n2 + b)], i] += np.sqrt((j2 + 1) / (jp2 + 1)) * cg(j2, m2, a, jp2) * cg(j2, n2, b, jp2)

    def xyz(Jz, Jp):
        return [(Jp + Jp.T) / 2 + 0j, (Jp - Jp.T) / (2j), Jz + 0j]

    Jm = xyz(Jz_m, Jp_m); Jn = xyz(Jz_n, Jp_n)
    SL = [-np.conj(x) for x in Jm]          # (Lambda_k f)(w) = f(k^-1 w): conjugate representation on the m index
    SR = Jn                                 # (P_k f)(w) = f(w k): standard representation on the n index
    return dict(d=d, B=B, idx=idx, C=C, SL=SL, SR=SR, M=M)


def single_checks(J2):
    o = pw_single(J2); M, SL, SR = o["M"], o["SL"], o["SR"]
    half = {1: 0.5, -1: -0.5}
    sig = [np.array([[0, 1], [1, 0]]) / 2, np.array([[0, -1j], [1j, 0]]) / 2, np.array([[1, 0], [0, -1]]) / 2]
    ab = [(1, 1), (1, -1), (-1, 1), (-1, -1)]; pos = {1: 0, -1: 1}
    err_R = err_L = 0.0
    for a in range(3):
        for (al, be) in ab:
            rhsR = sum(M[(al, ga)] * sig[a][pos[ga], pos[be]] for ga in (1, -1))
            rhsL = -sum(sig[a][pos[al], pos[ga]] * M[(ga, be)] for ga in (1, -1))
            err_R = max(err_R, np.abs(SR[a] @ M[(al, be)] - M[(al, be)] @ SR[a] - rhsR).max())
            err_L = max(err_L, np.abs(SL[a] @ M[(al, be)] - M[(al, be)] @ SL[a] - rhsL).max())
    # conj(D_ab) = (-1)^(a-b) D_{-a,-b}  =>  M_ab^T = (+-) M_{-a,-b}
    err_c = max(np.abs(M[(al, be)].T - (1 if al == be else -1) * M[(-al, -be)]).max() for (al, be) in ab)
    # unitarity sum_b D_ab conj(D_cb) = delta_ac, exact on states below the cutoff
    low = [i for i, b in enumerate(o["B"]) if b[0] < J2]
    err_u = 0.0
    for al in (1, -1):
        for ga in (1, -1):
            X = sum(M[(al, be)] @ M[(ga, be)].T for be in (1, -1)) - (1.0 if al == ga else 0.0) * np.eye(o["d"])
            err_u = max(err_u, np.abs(X[np.ix_(low, low)]).max() if J2 > 1 else 0.0)
    # trace: M_++ + M_-- must reproduce the character rule chi_j chi_1/2 = chi_{j-1/2} + chi_{j+1/2}
    return dict(J=J2 / 2, covariance_right=float(err_R), covariance_left=float(err_L), conj_rule=float(err_c), unitarity=float(err_u))


def cell_ops(J2):
    """Cell operators on the truncated cell space (all five link fluxes <= J2/2), as real sparse matrices in the
    joint eigenbasis of the commuting labels (C_B, C_T, C_P, C_b'', C_t'', and four magnetic numbers)."""
    o = pw_single(J2); d = o["d"]; I = np.eye(d)
    k3 = lambda a, b, c: np.kron(np.kron(a, b), c)          # ordering (B, T, P)
    onB = lambda X: k3(X, I, I); onT = lambda X: k3(I, X, I); onP = lambda X: k3(I, I, X)
    re = lambda X: np.real_if_close(X, tol=1e6).real
    SLz, SRz = re(o["SL"][2]), re(o["SR"][2])
    SLp, SRp = re(o["SL"][0] + 1j * o["SL"][1]), re(o["SR"][0] + 1j * o["SR"][1])      # raising parts, real
    Gb2z, Gb2p = onB(SLz) + onP(SLz), onB(SLp) + onP(SLp)                               # left end of b''
    Gt2z, Gt2p = onT(SLz) + onP(SRz), onT(SLp) + onP(SRp)                               # left end of t''
    cas = lambda z, p: z @ z + 0.5 * (p @ p.T + p.T @ p)
    Cb1, Ct1, Cr = onB(o["C"]), onT(o["C"]), onP(o["C"])
    Cb2, Ct2 = cas(Gb2z, Gb2p), cas(Gt2z, Gt2p)
    K = (Cb2 + np.pi * Ct2 + np.sqrt(2) * Gb2z + np.sqrt(3) * Gt2z + np.sqrt(5) * onB(SRz) + np.sqrt(7) * onT(SRz)
         + np.e * Cb1 + np.sqrt(11) * Ct1 + np.sqrt(13) * Cr)
    w, V = np.linalg.eigh(K)
    Jc = J2 / 2 * (J2 / 2 + 1) + 1e-6
    b2 = np.einsum("ij,ij->j", V, Cb2 @ V); t2 = np.einsum("ij,ij->j", V, Ct2 @ V)
    V = V[:, (b2 <= Jc) & (t2 <= Jc)]

    def pr(X):
        Y = V.T @ X @ V; Y[np.abs(Y) < 1e-11] = 0.0
        return sp.csr_matrix(Y)

    M = o["M"]; pm = (1, -1)
    Qc = {}
    for a in pm:
        for b in pm:   # conj(Q_ab) = sum_cd B_ca conj(P_cd) conj(T_db), Q = B^-1 P T
            Qc[(a, b)] = pr(sum(k3(M[(c, a)], M[(dd, b)].T, M[(c, dd)].T) for c in pm for dd in pm))
    return dict(dc=V.shape[1], dprod=d ** 3, elec_half=pr(Cb1 + Cb2 + Ct1 + Ct2), elec_rung=pr(Cr),
                Qc=Qc, P={ab: pr(onP(M[ab])) for ab in M},
                Rbz=pr(onB(SRz)), Rbp=pr(onB(SRp)), Lbz=pr(Gb2z), Lbp=pr(Gb2p),
                Rtz=pr(onT(SRz)), Rtp=pr(onT(SRp)), Ltz=pr(Gt2z), Ltp=pr(Gt2p))


def cell_ring_linop(c, L, e, lam, mu):
    """H = sum_x o_x + sum_x [ 2 mu' (Rb_x . Lb_{x+1} + Rt_x . Lt_{x+1}) - (lam/2) sum_ab conj(Q_ab)_x P_ab,x+1 ],
    o = (e'/2 + mu') elec_half + e' elec_rung. Returns (H, Pen) as real LinearOperators; Pen is the midpoint
    penalty sum over midpoints of (sum of the two generators)^2."""
    dc = c["dc"]; ep = 4 * e / 3; mup = 4 * mu / 3
    bond = [(-(lam / 2), c["Qc"][ab], c["P"][ab]) for ab in c["Qc"]]
    pen = []
    for R_z, R_p, L_z, L_p in ((c["Rbz"], c["Rbp"], c["Lbz"], c["Lbp"]), (c["Rtz"], c["Rtp"], c["Ltz"], c["Ltp"])):
        pen += [(2.0, R_z, L_z), (1.0, R_p, L_p.T.tocsr()), (1.0, R_p.T.tocsr(), L_p)]
    shape = (dc,) * L

    def ax(v, x, A):
        t = np.moveaxis(v, x, 0); sh = t.shape
        return np.moveaxis((A @ t.reshape(dc, -1)).reshape(sh), 0, x)

    def mv_terms(vec, onsite, pairs):
        v = vec.reshape(shape); out = np.zeros(shape)
        for x in range(L):
            out += ax(v, x, onsite)
            for wgt, A, Bm in pairs:
                out += wgt * ax(ax(v, x, A), (x + 1) % L, Bm)
        return out.reshape(-1)

    o_h = (ep / 2) * c["elec_half"] + ep * c["elec_rung"]
    N = dc ** L
    Pen = LinearOperator((N, N), matvec=lambda v: mv_terms(np.real(v), c["elec_half"], pen), dtype=float)
    H = LinearOperator((N, N), matvec=lambda v: mv_terms(np.real(v), o_h, bond) + mup * mv_terms(np.real(v), c["elec_half"], pen), dtype=float)
    return H, Pen


def gauge_checks(c):
    """The plaquette bond must commute with the midpoint gauge generators (two-cell operators)."""
    dc = c["dc"]
    if dc > 60:
        return None
    I = sp.identity(dc)
    bond = sum(sp.kron(c["Qc"][ab], c["P"][ab]) for ab in c["Qc"]).toarray()
    errs = []
    for R_z, R_p, L_z, L_p in ((c["Rbz"], c["Rbp"], c["Lbz"], c["Lbp"]), (c["Rtz"], c["Rtp"], c["Ltz"], c["Ltp"])):
        for R, Lm in ((R_z, L_z), (R_p, L_p)):
            Gm = (sp.kron(R, I) + sp.kron(I, Lm)).toarray()
            errs.append(np.abs(Gm @ bond - bond @ Gm).max())
    return dict(bond_symmetric=float(np.abs(bond - bond.T).max()), commutator_with_midpoint_gauge=float(max(errs)))


if __name__ == "__main__":
    res = {}
    for J2 in (1, 2, 3):
        r = single_checks(J2); res[f"single_J{J2}"] = r; print(json.dumps(r), flush=True)
    e, lam, mu = 1.0, 0.8, 12.0
    cases = [(2, 1), (3, 1), (2, 2)] if len(sys.argv) < 2 else [tuple(int(t) for t in a.split(",")) for a in sys.argv[1:]]
    for (L, J2) in cases:
        t0 = time.time()
        basis, H, W = sn_hamiltonian(L, J2, e, lam)
        herm = float(abs(H - H.T).max())
        wsn = np.linalg.eigvalsh(H.toarray()) if H.shape[0] <= 4000 else np.sort(eigsh(H, k=30, which="SA", return_eigenvectors=False))
        t1 = time.time()
        c = cell_ops(J2)
        gc = gauge_checks(c)
        Hc, Pen = cell_ring_linop(c, L, e, lam, mu)
        k = min(len(wsn), 16)
        wc, Vc = eigsh(Hc, k=k + 4, which="SA", tol=1e-10, ncv=min(Hc.shape[0] - 1, 3 * k + 30))
        order = np.argsort(wc); wc, Vc = wc[order], Vc[:, order]
        pen = np.array([float(Vc[:, i] @ Pen.matvec(Vc[:, i])) for i in range(len(wc))])
        phys = wc[pen < 1e-6]
        us = np.array(sorted(set(np.round(wsn, 7)))); uc = np.array(sorted(set(np.round(phys, 7))))
        m = min(len(us), len(uc)) - 1
        rec = dict(L=L, J=J2 / 2, sn_dim=len(basis), cell_dim=c["dc"], ring_dim=c["dc"] ** L, sn_symmetric=herm, gauge=gc,
                   n_phys_found=int((pen < 1e-6).sum()), distinct_compared=int(m),
                   max_diff=float(np.abs(us[:m] - uc[:m]).max()) if m > 0 else None,
                   sn_levels=[round(float(x), 6) for x in us[:8]], cell_levels=[round(float(x), 6) for x in uc[:8]],
                   sec=(round(t1 - t0, 1), round(time.time() - t1, 1)))
        res[f"compare_L{L}_J{J2}"] = rec; print(json.dumps(rec), flush=True)
        json.dump(res, open("su2_plaq_checks.json", "w"), indent=1)
