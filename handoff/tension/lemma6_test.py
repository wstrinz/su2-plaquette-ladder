"""Falsification test of Lemma 6 at ONE flux cutoff (3/2) on 2, 4 and 6 plaquettes (floats).
  (i)   E-(L)/L is nondecreasing in even L, in particular E-(L) >= (L/2) E-(2)
  (ii)  E+(L)/L <= [ (1/2) log Z+(2,b1) - (1/2) log Z+(2,b) + D(eps) ] / (b - b1)      for L = 4, 6
  (iii) the winding cost per plaquette (E-(L) - E+(L))/L is at least sigma for L = 2, 4, 6
Control: the same with D dropped from (ii); if the correction D were unnecessary this would still hold."""
import json, math, numpy as np
E = "../explore/"
L2 = {round(r["lam"], 2): r for r in json.load(open(E + "gaps_L2_J3.json"))}
L4 = {round(r["lam"], 2): r for r in json.load(open(E + "gaps_L4_J3h.json"))}
L6 = {round(r["lam"], 2): r for r in json.load(open(E + "gaps_L6_J3.json"))}
def logZ(spec, b):
    s = np.asarray(spec); e0 = s.min(); return -b * e0 + math.log(np.exp(-b * (s - e0)).sum())
def D(eps):
    e1 = eps * eps / (2 * (1 - eps) ** 2); return -0.25 * math.log(1 - eps) - 0.25 * math.log(1 - e1)
out = []; viol = 0; viol_ctrl = 0; cases = 0
for lam in sorted(L2):
    if lam not in L6 or lam == 0: continue
    ev = np.array(L2[lam]["spectrum_even"]); al = list(L2[lam]["spectrum"]); evl = list(ev); j = 0; od = []
    for x in al:
        if j < len(evl) and abs(x - evl[j]) < 1e-9: j += 1
        else: od.append(x)
    Ep = {2: ev.min(), 4: L4[lam]["E0"], 6: L6[lam]["E0"]}
    Em = {2: min(od), 4: L4[lam]["E0"] + L4[lam]["odd"][0], 6: L6[lam]["E0"] + L6[lam]["odd"][0]}
    for b in (8, 12, 20, 30):
        for b1 in (2, 3, 5):
            eps = 1 - math.exp(-b * Ep[4] - 2 * logZ(ev, b))
            if not (0 < eps < 0.5): continue
            core = (0.5 * logZ(ev, b1) - 0.5 * logZ(ev, b)) / (b - b1)
            up = core + D(eps) / (b - b1); sigma = Em[2] / 2 - up
            cases += 1
            ok = (Em[2] / 2 <= Em[4] / 4 + 1e-10 <= Em[6] / 6 + 2e-10) and all(Ep[L] / L <= up + 1e-10 for L in (4, 6)) and all((Em[L] - Ep[L]) / L >= sigma - 1e-10 for L in (2, 4, 6))
            viol += not ok
            viol_ctrl += not all(Ep[L] / L <= core + 1e-10 for L in (4, 6))
            out.append(dict(lam=lam, beta=b, beta1=b1, eps=eps, Eplus_upper=up, margin4=up - Ep[4] / 4, margin6=up - Ep[6] / 6, control_margin4=core - Ep[4] / 4, sigma=sigma,
                            winding_cost=[(Em[L] - Ep[L]) / L for L in (2, 4, 6)], Eminus_per=[Em[L] / L for L in (2, 4, 6)], ok=ok))
print(f"{cases} cases (6 couplings x temperatures), violations: {viol}; control with D dropped violated in {viol_ctrl}")
print("smallest margins of (ii):", min(r["margin4"] for r in out), min(r["margin6"] for r in out))
json.dump(dict(cases=cases, violations=viol, control_violations=viol_ctrl, rows=out), open("lemma6_test.json", "w"), indent=1)
