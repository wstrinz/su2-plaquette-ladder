"""Exploration (floats): the string-tension bound of Lemma 6 with exact inputs, and falsification tests of its two halves.

  E-(L) >= -(L / (2 b3)) log Z-(2, b3)                                            (le_rpow for the odd sector, any b3)
  E+(L) <=  L [ (1/2) log Z+(2, b1) - (1/2) log Z+(2, b) + D(eps) ] / (b - b1)      (b1 < b; eps >= 1 - Z+(4, b)/Z+(2, b)^2)
  D(eps) = -(1/4) log(1 - eps) - (1/4) log(1 - eps1),  eps1 = eps^2 / (2 (1 - eps)^2)
so  E-(L) - E+(L) >= sigma L  for every even L >= 2.
"""
import json, math
import numpy as np
E = "../explore/"
L2 = {round(r["lam"], 2): r for r in json.load(open(E + "gaps_L2_J6.json"))}
L4 = {round(r["lam"], 2): r for r in json.load(open(E + "gaps_L4_J4.json"))}
L4b = {round(r["lam"], 2): r for r in json.load(open(E + "gaps_L4_J5.json")) + json.load(open(E + "gaps_L4_J5b.json"))}
L6 = {round(r["lam"], 2): r for r in json.load(open(E + "gaps_L6_J3.json"))}

def logZ(spec, beta):
    s = np.asarray(spec); e0 = s.min()
    return -beta * e0 + math.log(np.exp(-beta * (s - e0)).sum())

def D(eps):
    e1 = eps * eps / (2 * (1 - eps) ** 2)
    return -0.25 * math.log(1 - eps) - 0.25 * math.log(1 - e1)

rows = []
for lam in sorted(L2):
    if lam not in L4 or abs(lam - round(lam)) > 1e-9 and lam > 1:
        continue
    r2 = L2[lam]; r4 = L4b.get(lam, L4[lam])
    ev = np.array(r2["spectrum_even"]); al = np.array(r2["spectrum"])
    # odd spectrum = all minus even (multiset difference)
    od = []
    ev_sorted = list(ev); j = 0
    for x in al:
        if j < len(ev_sorted) and abs(x - ev_sorted[j]) < 1e-9:
            j += 1
        else:
            od.append(x)
    od = np.array(od); assert len(od) + len(ev) == len(al)
    Ep2, Em2, Ep4 = ev.min(), od.min(), r4["E0"]
    best = None
    for b in (6, 8, 10, 12, 16, 20, 30):
        eps = 1 - math.exp(-b * Ep4 - 2 * logZ(ev, b))
        if not (0 < eps < 0.3):
            continue
        for b1 in (2, 3, 4, 5, 6, 8):
            if b1 >= b:
                continue
            up = (0.5 * logZ(ev, b1) - 0.5 * logZ(ev, b) + D(eps)) / (b - b1)
            if best is None or up < best[0]:
                best = (up, b, b1, eps)
    lows = {b3: -logZ(od, b3) / (2 * b3) for b3 in (6, 10, 20, 40)}
    up, b, b1, eps = best
    sigma = lows[20] - up
    row = dict(lam=lam, half_gap=(Em2 - Ep2) / 2, sigma_ideal=sigma, eplus_up=up, eplus2_half=Ep2 / 2, e4_quarter=Ep4 / 4, beta=b, beta1=b1, eps=eps,
               eminus_low_b20=lows[20], eminus2_half=Em2 / 2, torelon_L4_per=r4["odd"][0] / 4,
               torelon_L6_per=(L6[lam]["odd"][0] / 6 if lam in L6 else None))
    # falsification: E-(L)/L nondecreasing; E+(4)/4 <= bound
    row["test_minus_monotone_2_4"] = (r4["E0"] + r4["odd"][0]) / 4 - Em2 / 2
    row["test_plus_upper_4"] = up - Ep4 / 4
    if lam in L6:
        row["test_minus_monotone_4_6"] = (L6[lam]["E0"] + L6[lam]["odd"][0]) / 6 - (L4[lam]["E0"] + L4[lam]["odd"][0]) / 4
        row["test_plus_upper_6"] = up - L6[lam]["E0"] / 6
    rows.append(row)
    print(f"lam {lam:5.2f}  (E-(2)-E+(2))/2 {row['half_gap']:.4f}  sigma {sigma:.4f} (beta {b}, beta1 {b1}, eps {eps:.4f}; E+ slack {up - Ep2 / 2:.5f}, E- slack {Em2 / 2 - lows[20]:.5f})"
          f"  winding cost per plaquette L=4 {row['torelon_L4_per']:.4f}" + (f" L=6 {row['torelon_L6_per']:.4f}" if row['torelon_L6_per'] else "")
          + f"  tests: {row['test_minus_monotone_2_4']:+.4f} {row['test_plus_upper_4']:+.5f}" + (f" {row['test_minus_monotone_4_6']:+.4f} {row['test_plus_upper_6']:+.5f}" if lam in L6 else ""))
json.dump(rows, open("tension_float.json", "w"), indent=1)
