"""Tiling of [0, 12] for the string-tension theorem. Width 1/20 up to lambda = 6 and 1/10 beyond; beta1 = 3;
beta = 20 up to lambda = 10, 16 beyond.
Cutoffs as in Theorem B. None of these choices is trusted."""
import json
from fractions import Fraction as Fr
out = []; x = Fr(0)
while x < 12:
    d = Fr(1, 20) if x < 6 else Fr(1, 10)
    js2, jt2 = (5, 4) if x < 6 else (6, 5)
    out.append(dict(la=str(x), lb=str(x + d), beta="20" if x < 10 else "16", beta1="3", js2=js2, jt2=jt2, c="12")); x += d
json.dump(out, open("tiling.json", "w"), indent=0); print(len(out))
