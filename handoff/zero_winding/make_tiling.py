"""Tiling of [0, 12] for the zero-winding theorem, with the inverse temperature and cutoffs used on each interval.
Nothing here is trusted: any choice of beta, cutoffs and c gives valid bounds; the choices only affect how good they are."""
import json
from fractions import Fraction as Fr
knots = [(Fr(0), Fr(13, 4)), (Fr(1, 4), Fr(13, 4)), (Fr(1, 2), Fr(31, 10)), (Fr(1), Fr(27, 10)), (Fr(3, 2), Fr(12, 5)), (Fr(2), Fr(41, 20)),
         (Fr(3), Fr(19, 10)), (Fr(4), Fr(7, 4)), (Fr(5), Fr(17, 10)), (Fr(6), Fr(33, 20)), (Fr(12), Fr(33, 20))]
def beta_at(x):
    for (x0, y0), (x1, y1) in zip(knots, knots[1:]):
        if x0 <= x <= x1:
            return Fr(round((y0 + (y1 - y0) * (x - x0) / (x1 - x0)) * 20), 20)
def block(lam):                      # beta is constant on blocks so that neighbouring intervals share their endpoint bounds
    if lam < 2:  w = Fr(1, 4)
    elif lam < 6: w = Fr(1, 2)
    else: return (Fr(6), Fr(12))
    k = lam // w; return (k * w, (k + 1) * w)
segs = [(Fr(0), Fr(1), Fr(1, 320)), (Fr(1), Fr(2), Fr(1, 160)), (Fr(2), Fr(6), Fr(1, 40)), (Fr(6), Fr(12), Fr(1, 20))]
out = []
for a, b, d in segs:
    x = a
    while x < b:
        lo, hi = block(x); beta = beta_at((lo + hi) / 2)
        js2, jt2 = (5, 4) if x < 6 else (6, 5)
        out.append(dict(la=str(x), lb=str(x + d), beta=str(beta), js2=js2, jt2=jt2, c="12")); x += d
assert out[0]["la"] == "0" and out[-1]["lb"] == "12" and all(p["lb"] == q["la"] for p, q in zip(out, out[1:]))
json.dump(out, open("tiling.json", "w"), indent=0)
print(len(out), "intervals;", len({(p["beta"]) for p in out}), "distinct betas:", sorted({Fr(p["beta"]) for p in out}))
