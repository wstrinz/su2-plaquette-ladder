"""The corollary of Theorems B and C, from the two Lean certificates: with g+ the certified gap of Theorem B
(sector c = +1) the full gauge-invariant spectrum on every even ring of length L >= 2 has gap >= min(g+, L sigma)."""
import json, math
from fractions import Fraction as Fr
cert = json.load(open("tension_certificate.json"))      # written by gen_lean_tension.py together with the Lean file
assert Fr(cert[0]["la"]) == 0 and all(Fr(a["lb"]) == Fr(b["la"]) for a, b in zip(cert, cert[1:]))
B = json.load(open("../zero_winding/even_lean_bounds.json"))
gB = [(Fr(a), Fr(b), g) for a, b, g in zip(B["la"], B["lb"], B["bounds"])]
def sig(lo, hi): return min(float(Fr(c["sigma"])) for c in cert if Fr(c["la"]) < hi and Fr(c["lb"]) > lo)
def gp(lo, hi): return min(g for a, b, g in gB if a < hi and b > lo)
ranges = [(0, Fr(1, 2)), (Fr(1, 2), 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 8), (8, 10), (10, 12)]
out = []
for lo, hi in ranges:
    s, g = sig(lo, hi), gp(lo, hi)
    out.append(dict(range=f"[{lo},{hi}]", sigma=s, g_plus=round(g, 4), full_gap_L2=round(min(g, 2 * s) - 5e-5, 4), full_gap_L_ge_4=round(min(g, 4 * s) - 5e-5, 4)))
    print(out[-1])
# finest common refinement for the overall minimum
pts = sorted({a for a, b, g in gB} | {b for a, b, g in gB} | {Fr(c["la"]) for c in cert} | {Fr(c["lb"]) for c in cert})
full = min(min(gp(a, b), 2 * sig(a, b)) for a, b in zip(pts, pts[1:]))
print("minimum over [0, 12] of min(g+, 2 sigma):", full, "  minimum sigma:", min(float(Fr(c['sigma'])) for c in cert))
json.dump(dict(ranges=out, min_full_gap=full), open("corollary_full_gap.json", "w"), indent=1)
