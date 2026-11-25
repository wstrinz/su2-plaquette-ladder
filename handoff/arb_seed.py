"""Ball-arithmetic (Arb) seed enclosures and gap bound for a gauge-Higgs ring at n0 = 2.

Everything from the exact rational Hamiltonian to the final bound is evaluated in Arb balls,
so the printed bound is rigorous GIVEN the theorem (uniform gap from seed purities for a real
reflection-positive ring with even n0 >= 2) and the correctness of Arb/python-flint.
"""
import sys, time, json
from fractions import Fraction
import numpy as np
from flint import arb, arb_mat, fmpz_mat, fmpq, ctx
from lib import cyclic, s3, q8, gen_set, gauge_higgs_chain, ring_hamiltonian

ctx.prec = 256


def exact_checks(G, m, e, kappa, scale):
    """Integer checks: scale*H is integral, and the reflection-positive cell structure is exact."""
    S, F = gen_set(G), np.rint(G.F()).astype(np.int64)
    R = {h: np.rint(G.R(h)).astype(np.int64) for h in S}
    Lm = {h: np.rint(G.Lm(h)).astype(np.int64) for h in S}
    ok = all(np.array_equal(Lm[h], F @ R[h] @ F) for h in S)            # L_h = F R_h F
    ok &= np.array_equal(F @ F, np.eye(G.n, dtype=np.int64)) and np.array_equal(F, F.T)
    # sum_h R_h (x) F R_h F  ==  sum_h [Sym_h (x) F Sym_h F + Asym_h (x) F Asym_h F]   (times 4)
    lhs = sum(np.kron(R[h], F @ R[h] @ F) for h in S) * 4
    rhs = sum(np.kron(R[h] + R[h].T, F @ (R[h] + R[h].T) @ F) + np.kron(R[h] - R[h].T, F @ (R[h] - R[h].T) @ F)
              for h in S)
    ok &= np.array_equal(lhs, rhs)
    d, bp, o = gauge_higgs_chain(G, float(m), float(e), float(kappa))
    oi = np.rint(o * scale)
    ok &= np.allclose(o * scale, oi) and np.array_equal(F @ oi.astype(np.int64) @ F, oi.astype(np.int64))
    ok &= np.array_equal(oi, oi.T)
    return bool(ok)


def int_hamiltonian(G, L, m, e, kappa, scale):
    d, bp, o = gauge_higgs_chain(G, float(m), float(e), float(kappa))
    H = ring_hamiltonian(L, d, bp, o).toarray() * scale
    Hi = np.rint(H)
    assert np.abs(H - Hi).max() < 1e-9, "scale does not clear denominators"
    assert np.array_equal(Hi, Hi.T)
    return Hi.astype(np.int64)


def partition_pair(Hi, scale, beta):
    """Enclosures of Z(beta) = Tr e^{-beta H} and Z(2 beta), with H = Hi/scale exact."""
    n = Hi.shape[0]
    A = arb_mat(fmpz_mat(n, n, [int(x) for x in Hi.reshape(-1)])) * (arb(-1) * arb(fmpq(beta.numerator, beta.denominator)) / (2 * scale))
    E = A.exp()                       # e^{-beta H / 2}
    E2 = E * E                        # e^{-beta H}
    Zb = E2.trace()
    Z2b = sum((E2[i, j] * E2[j, i] for i in range(n) for j in range(n)), arb(0)) if n <= 64 else (E2 * E2).trace()
    return Zb, Z2b


def zdef(a, b):
    return b + a * (2 - a) * (1 - b)


def fsq(z):
    return z * z / (2 * (1 - z) ** 2)


def up(x):
    return x.mid() + x.rad() if hasattr(x, "rad") else x


def certified_bound(es, et, beta, J=48):
    """Mirror of the core's certified_gap_bound in Arb. Returns a rigorous lower bound or None."""
    zstar, half, eps_low = 2 - arb(2).sqrt(), arb(1) / 2, arb(12731) / 100000
    s, t = es, et
    b = arb(fmpq(beta.numerator, beta.denominator))
    adm = False
    for j in range(J + 1):
        z = zdef(s, t)
        if not (z < half):
            return None
        if (s < eps_low) and (t < eps_low):
            adm = True
        if j == J:
            r = z / (1 - z)
            if not adm or not (r <= arb(1) / 10):
                return None
            bJ = -r.log() / (b * arb(2) ** J)
            tail = arb(5).log() / (b * arb(2) ** J)
            return (bJ - tail)
        if not (z < zstar):
            return None
        s2 = fsq(z)
        z2 = zdef(t, s2)
        if not (z2 < zstar):
            return None
        s, t = s2, fsq(z2)


def certify(G, m, e, kappa, beta, scale):
    t0 = time.time()
    assert exact_checks(G, m, e, kappa, scale), "exact RP checks failed"
    H2, H4 = int_hamiltonian(G, 2, m, e, kappa, scale), int_hamiltonian(G, 4, m, e, kappa, scale)
    Z2, _ = partition_pair(H2, scale, beta)
    Z4, Z4d = partition_pair(H4, scale, beta)
    es, et = 1 - Z4 / (Z2 * Z2), 1 - Z4d / (Z4 * Z4)
    # upper ends as exact-ish balls; the recurrence is order preserving
    es_u, et_u = arb(es.mid() + es.rad()), arb(et.mid() + et.rad())
    assert es_u > 0 and et_u > 0
    bound = certified_bound(es_u, et_u, beta)
    out = dict(G=G.name, m=str(m), e=str(e), kappa=str(kappa), n0=2, beta0=str(beta),
               eps_s=es.str(20), eps_t=et.str(20),
               bound=None if bound is None else bound.str(15),
               bound_lower=None if bound is None else float((bound.mid() - bound.rad()).str(30, radius=False)),
               seconds=round(time.time() - t0, 1), prec=ctx.prec)
    print(json.dumps(out), flush=True)
    return out


if __name__ == "__main__":
    which = sys.argv[1]
    Fr = Fraction
    res = []
    if which == "z3":
        for e, k, b in ((2, 1, Fr(3, 2)), (1, 1, 2), (1, Fr(1, 2), Fr(5, 2)), (4, 1, Fr(5, 4))):
            res.append(certify(cyclic(3), Fr(1), Fr(e), Fr(k), Fr(b), 4))
    elif which == "s3":
        for e, k, b in ((2, 1, Fr(5, 2)), (1, Fr(1, 2), Fr(15, 4)), (4, 1, 2), (1, 1, 3)):
            res.append(certify(s3(), Fr(1), Fr(e), Fr(k), Fr(b), 6))
    elif which == "q8-2ring":
        pass
    json.dump(res, open(f"arb_{which}.json", "w"), indent=1)
