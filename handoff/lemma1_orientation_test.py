"""Falsification test for split-link positivity (Lemma 1), SU(2), position representation.
Checks by random sampling the pointwise identities the proof rests on. Any sign or orientation error
(e.g. the reflected line being the adjoint of the right one) would show up as O(1) failures."""
import numpy as np
rng = np.random.default_rng(7)
s = [np.eye(2), np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.array([[1, 0], [0, -1]])]
def su2():
    q = rng.normal(size=4); q /= np.linalg.norm(q)
    return q[0] * s[0] + 1j * (q[1] * s[1] + q[2] * s[2] + q[3] * s[3])
quat = lambda U: np.array([U.trace().real / 2] + [(-1j * (U @ s[k])).trace().real / 2 for k in (1, 2, 3)])
inv = lambda U: U.conj().T
# a cell: b1 (left-bottom midpoint -> vertex), b2 (vertex -> right-bottom midpoint), t1, t2 on top, r (bottom -> top vertex)
cell = lambda: dict(b1=su2(), b2=su2(), t1=su2(), t2=su2(), r=su2())
rho = lambda c: dict(b1=inv(c["b2"]), b2=inv(c["b1"]), t1=inv(c["t2"]), t2=inv(c["t1"]), r=c["r"])
Pline = lambda c: inv(c["b2"]) @ c["r"] @ c["t2"]          # right-bottom midpoint -> right-top midpoint
Qline = lambda c: c["b1"] @ c["r"] @ inv(c["t1"])          # left-bottom midpoint -> left-top midpoint
worst = dict(loop=0, refl=0, real=0, gaugeW=0, intertw=0, vertex=0, wrong_sign=np.inf)
for _ in range(2000):
    x, y = cell(), cell()                                   # cells x and x+1
    # Wilson loop of the plaquette between rungs x and x+1, written with the unsplit leg links
    W = (x["b2"] @ y["b1"] @ y["r"] @ inv(y["t1"]) @ inv(x["t2"]) @ inv(x["r"])).trace()
    p, q = quat(Pline(x)), quat(Qline(y))
    worst["loop"] = max(worst["loop"], abs(W - 2 * p @ q)); worst["real"] = max(worst["real"], abs(W.imag))
    worst["refl"] = max(worst["refl"], np.abs(Pline(rho(y)) - Qline(y)).max())        # Q = P o rho
    worst["wrong_sign"] = min(worst["wrong_sign"], abs(W - 2 * (p[0] * q[0] - p[1:] @ q[1:])))  # the adjoint variant must FAIL
    h = su2(); x2, y2 = dict(x), dict(y); x2["b2"] = x["b2"] @ inv(h); y2["b1"] = h @ y["b1"]   # midpoint gauge transformation
    W2 = (x2["b2"] @ y2["b1"] @ y2["r"] @ inv(y2["t1"]) @ inv(x2["t2"]) @ inv(x2["r"])).trace()
    worst["gaugeW"] = max(worst["gaugeW"], abs(W - W2))
    worst["intertw"] = max(worst["intertw"], np.abs(rho(x2)["b1"] - h @ rho(x)["b1"]).max())   # rho carries right action on b2 to left action on b1
    g = su2(); x3 = dict(x); x3["b1"] = x["b1"] @ inv(g); x3["b2"] = g @ x["b2"]; x3["r"] = g @ x["r"]   # bottom-vertex gauge
    worst["vertex"] = max(worst["vertex"], np.abs(Pline(x3) - Pline(x)).max(), np.abs(Qline(x3) - Qline(x)).max())
print({k: float("%.2e" % v) for k, v in worst.items()})
