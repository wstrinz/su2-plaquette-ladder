"""Exploration (floats; not a certificate): what the two-plaquette seed can give with exact inputs.
Ideal seeds of the scheme used in the note, with nothing lost to the truncation inequality or to rounding:
    eps_s = 1 - exp(-beta E0(4)) / Z_2(beta)^2,      eps_t = 1 - exp(-2 beta E0(4)) / Z_2(beta)^4,
with Z_2 from the full two-plaquette spectrum at cutoff 3 and E0(4) from Lanczos at cutoff 2 (or 5/2 where available).
They go through the same two-purity recurrence (arb_seed.certified_bound) and beta is optimised on a grid.
Also: the convexity of log Z_2 in lambda (Lemma 4 (b)) checked by second differences."""
import json, sys, math
sys.path.insert(0, "..")
from fractions import Fraction as Fr
import numpy as np
from flint import arb
from arb_seed import certified_bound

L2 = {round(r["lam"], 2): r for r in json.load(open("gaps_L2_J6.json"))}
L2b = {round(r["lam"], 2): r for r in json.load(open("gaps_L2_J7.json"))}
L4 = {round(r["lam"], 2): r for r in json.load(open("gaps_L4_J4.json"))}
L4b = {round(r["lam"], 2): r for r in json.load(open("gaps_L4_J5.json")) + json.load(open("gaps_L4_J5b.json"))}
L4c = {round(r["lam"], 2): r for r in json.load(open("gaps_L4_J3.json"))}
betas = [Fr(n, 20) for n in range(10, 201)]

def logZ(spec, beta):
    s = np.array(spec); e0 = s.min()
    return -beta * e0 + math.log(np.exp(-beta * (s - e0)).sum())

def best(spec, e04):
    out = (None, None, None, None)
    for b in betas:
        bf = float(b); l = logZ(spec, bf)
        es = 1 - math.exp(-bf * e04 - 2 * l); et = 1 - math.exp(-2 * bf * e04 - 4 * l)
        if es <= 0 or et <= 0:
            continue
        g = certified_bound(arb(es), arb(et), b)
        if g is not None and (out[0] is None or float(g.mid()) > out[0]):
            out = (float(g.mid()), bf, es, et)
    return out

rows = []
for lam in sorted(L2):
    if lam not in L4:
        continue
    r2, r4 = L2[lam], L4[lam]
    hi = L4b.get(lam, r4)
    e04 = hi["E0"]; cut = 2.5 if lam in L4b else 2.0
    # Aitken extrapolation in the cutoff where three cutoffs are available (rough indication of the cutoff error)
    e04x = None
    if lam in L4b and lam in L4c:
        d1 = r4["E0"] - L4c[lam]["E0"]; d2 = hi["E0"] - r4["E0"]
        if abs(d1) > 1e-9 and abs(d2 / d1) < 1:
            e04x = hi["E0"] + d2 * (d2 / d1) / (1 - d2 / d1)
    use = e04x if e04x is not None else e04
    g, b, es, et = best(r2["spectrum"], use)
    ge, be, ese, ete = best(r2["spectrum_even"], use)
    dE = use - 2 * r2["E0"]
    rows.append(dict(lam=lam, torelon_L2=r2["odd"][0], even_L2=r2["even"][0], torelon_L4=hi["odd"][0], even_L4=hi["even"][0],
                     E0_4=e04, E0_4_cutoff=cut, E0_4_extrapolated=e04x, E0_4_minus_2E0_2=dE,
                     ideal_bound=g, ideal_beta=b, ideal_eps_s=es, ideal_eps_t=et,
                     ideal_bound_even=ge, ideal_beta_even=be, ideal_eps_s_even=ese, ideal_eps_t_even=ete))
    f = lambda x: "none" if x is None else f"{x:.4f}"
    print(f"lam {lam:5.2f}  L=2 torelon {r2['odd'][0]:.4f} even {r2['even'][0]:.4f} | L=4 torelon {hi['odd'][0]:.4f} even {hi['even'][0]:.4f} | dE {dE:+.5f}"
          f" (cutoff shift {0 if e04x is None else e04x - e04:+.5f}) | ideal bound {f(g)} (beta {b}) | even-sector ideal bound {f(ge)} (beta {be}, eps_s {f(ese)})", flush=True)

# cutoff check of Z_2: cutoff 3 against 7/2
zc = {}
for lam, r in L2b.items():
    if lam in L2:
        zc[lam] = max(abs(logZ(r["spectrum"], b) - logZ(L2[lam]["spectrum"], b)) for b in (1.0, 2.0, 4.0))
# Lemma 4 (b): second differences of log Z_2 in lambda on the 0.25 grid
lams = sorted(L2); worst = math.inf
for b in (1.0, 2.0, 3.75, 6.0):
    l = [logZ(L2[x]["spectrum"], b) for x in lams]
    worst = min(worst, min(l[i - 1] - 2 * l[i] + l[i + 1] for i in range(1, len(l) - 1)))
print("log Z_2 cutoff 3 vs 7/2, max difference:", zc)
print("smallest second difference of log Z_2 in lambda:", worst)
json.dump(dict(rows=rows, logZ2_cutoff_check=zc, convexity_min_second_difference=worst, betas="1.00 to 10.00 step 0.05"), open("horizon.json", "w"), indent=1)
