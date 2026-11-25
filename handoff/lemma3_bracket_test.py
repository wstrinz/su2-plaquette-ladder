"""Falsification test of the truncation inequality (Lemma 3) for the ladder, float.
For L = 2 and several (j*, c, lam, beta): the right side must dominate Z^(J)(2, beta) at every cutoff J >= j*.
A deliberately wrong variant (correction term dropped) is run alongside: it must FAIL somewhere, or the test has no teeth."""
import itertools, json, numpy as np
import su2_plaq
L, e = 2, 1.0; ep = 4 * e / 3; JMAX2 = 6
ops = {J2: su2_plaq.sn_hamiltonian(L, J2, e, 1.0) for J2 in range(1, JMAX2 + 1)}        # basis, H(lam=1), W
def parts(J2):
    basis, H1, W = ops[J2]; W = W.toarray(); H0 = (H1.toarray() + W); return basis, H0, W   # H = H0 - lam W
def Z(J2, lam, beta):
    basis, H0, W = parts(J2); return np.exp(-beta * np.linalg.eigvalsh(H0 - lam * W)).sum()
def label_sum(J2, beta):
    basis, H0, W = parts(J2); return np.exp(-beta * np.diag(H0)).sum()
SALL = lambda beta: label_sum(JMAX2, beta) * (1 + 1e-9)            # float stand-in for the full label sum (tail beyond J = 3 is < 1e-9 here)
def rhs(js2, c, lam, beta, correction=True):
    basis, H0, W = parts(js2 + 1); inP = np.array([max(st) <= js2 for st in basis]); P = np.diag(inP.astype(float)); Qp = np.eye(len(basis)) - P
    A = P @ (H0 - lam * W) @ P - (lam ** 2 / c if correction else 0.0) * P @ W @ Qp @ W @ P
    A = A[np.ix_(inP, inP)]
    return np.exp(-beta * np.linalg.eigvalsh(A)).sum() + np.exp(beta * (lam * L + c)) * (SALL(beta) - label_sum(js2, beta))
rows, bad, bad_wrong = [], 0, 0
for js2, c, lam, beta in itertools.product((1, 2, 3), (2.0, 6.0, 12.0), (0.5, 2.0, 5.0), (1.5, 4.0)):
    r, rw = rhs(js2, c, lam, beta), rhs(js2, c, lam, beta, correction=False)
    zs = [Z(J2, lam, beta) for J2 in range(js2, JMAX2 + 1)]
    ok = all(z <= r * (1 + 1e-12) for z in zs); okw = all(z <= rw * (1 + 1e-12) for z in zs)
    bad += not ok; bad_wrong += not okw
    rows.append(dict(jstar=js2 / 2, c=c, lam=lam, beta=beta, ok=bool(ok), slack=float(np.log(r / max(zs))), wrong_variant_ok=bool(okw)))
print(json.dumps(dict(cases=len(rows), violations=bad, wrong_variant_violations=bad_wrong, tightest_log_slack=min(r["slack"] for r in rows), median_log_slack=float(np.median([r["slack"] for r in rows])))))
json.dump(rows, open("lemma3_bracket_test.json", "w"), indent=1)
