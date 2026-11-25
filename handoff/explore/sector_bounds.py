"""EXPLORATION driver for the zero-winding sector: picks beta per interval, runs sector_bounds.jl (rigorous interval
seeds, same Lemma 3 / Lemma 4 machinery restricted to the sector), and turns the seeds into bounds with the Arb mirror
of the two-purity recurrence (arb_seed.certified_bound). No Lean file is generated and nothing here is replayed by a
second implementation.   usage: sector_bounds.py scan | full"""
import json, subprocess, sys
sys.path.insert(0, "..")
from fractions import Fraction as Fr
from flint import arb
from arb_seed import certified_bound
JL = ["/home/claude/julia/julia-1.12.4/bin/julia", "-t", "2", "--project=/home/claude/ext/CertifiedGaps/code/julia", "sector_bounds.jl"]
fs = lambda q: str(Fr(q))

def tiling():
    pts = [Fr(i, 80) for i in range(0, 160)] + [Fr(2) + Fr(i, 20) for i in range(0, 81)]
    return list(zip(pts[:-1], pts[1:]))

def run(out, jobs, sector="even"):
    p = subprocess.run(JL + [out, sector] + [f"{fs(a)}:{fs(b)}:{fs(be)}:{js}:{jt}:{fs(c)}" for a, b, be, js, jt, c in jobs], capture_output=True, text=True)
    assert p.returncode == 0, p.stderr[-800:]
    rows = json.load(open(out))
    for r in rows:
        g = certified_bound(arb(r["eps_s"]), arb(r["eps_t"]), Fr(r["beta"]))
        r["bound"] = None if g is None else float(g.lower())
    json.dump(rows, open(out, "w"), indent=1)
    return rows

ideal = {round(r["lam"], 2): r for r in json.load(open("horizon.json"))["rows"]}
if sys.argv[1] == "scan":
    # sample intervals, narrow enough that the interval slack of Lemma 4 (about beta |E0''| d^2) is small
    jobs = []
    for lam in (Fr(0), Fr(1, 4), Fr(1, 2), Fr(1), Fr(3, 2), Fr(2), Fr(3), Fr(4), Fr(5), Fr(6)):
        b0 = Fr(round(min(ideal[round(float(lam), 2)]["ideal_beta_even"], 6.0) * 20), 20)
        d = Fr(1, 320) if lam <= 1 else (Fr(1, 160) if lam < 2 else Fr(1, 40))
        la = lam if lam < 6 else lam - d
        for db in (-Fr(9, 10), -Fr(3, 5), -Fr(3, 10), -Fr(3, 20), Fr(0), Fr(3, 20), Fr(3, 10)):
            if b0 + db >= 1:
                jobs.append((la, la + d, b0 + db, 5, 4, Fr(12)))
    rows = run("sector_scan.json", jobs)
    best = {}
    for r in rows:
        if r["bound"] is not None and (r["la"] not in best or r["bound"] > best[r["la"]][0]):
            best[r["la"]] = (r["bound"], r["beta"], r["eps_s"], r["eps_t"], r["lb"])
    for k in sorted(best, key=Fr):
        print(k, best[k])
    json.dump(best, open("sector_scan_best.json", "w"))
else:
    best = json.load(open("sector_scan_best.json"))
    knots = sorted((Fr(k), Fr(v[1])) for k, v in best.items())
    def beta_for(lam):
        if lam <= knots[0][0]:
            # towards lam = 0 the optimum grows; cap it
            return min(Fr(6), knots[0][1] + (knots[0][0] - lam) * 12)
        for (x0, y0), (x1, y1) in zip(knots, knots[1:]):
            if x0 <= lam <= x1:
                y = y0 + (y1 - y0) * (lam - x0) / (x1 - x0); return Fr(round(y * 20), 20)
        return knots[-1][1]
    jobs = [(a, b, beta_for(a), 5, 4, Fr(12)) for a, b in tiling()]
    rows = run("sector_even_intervals.json", jobs)
    cut = lambda lo, hi: min(r["bound"] if r["bound"] is not None else -1 for r in rows if Fr(r["la"]) >= Fr(lo) and Fr(r["lb"]) <= Fr(hi))
    summ = {f"[{lo},{hi}]": round(cut(lo, hi), 4) for lo, hi in (("0", "7/10"), ("7/10", "3/2"), ("3/2", "2"), ("2", "5/2"), ("5/2", "4"), ("4", "6"))}
    print(summ); json.dump(summ, open("sector_even_summary.json", "w"))
