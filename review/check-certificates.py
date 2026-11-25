"""Check the serialized replay outputs against Lean's literal tables. Python 3.10+."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / "handoff"
LEAN = DATA / "lean" / "GaugeGaps"


def rational(value):
    return Q(str(value).strip("() ").replace(" ", "").replace("//", "/"))


def records(path):
    return [json.loads(line, parse_float=Q) for line in path.read_text().splitlines() if line.strip()]


def check_tiling(table, end):
    assert table[0][0] == 0 and table[-1][1] == end
    assert all(a < b for a, b, *_ in table)
    assert all(left[1] == right[0] for left, right in zip(table, table[1:]))


def verify_gap(name, files, replay, end, count):
    pattern = r"⟨([^,]+), ([^,]+), ([^,]+), \{ s := \[([^,]+),.*?t := \[([^,]+),.*?r := ([^,]+),"
    table = [tuple(map(rational, row)) for path in files
             for row in re.findall(pattern, path.read_text(encoding="utf-8"))]
    assert len(table) == len(replay) == count
    check_tiling(table, end)
    suffix = "up" if name == "B" else "replay"
    for (a, b, beta, s, t, rate), row in zip(table, replay):
        assert (a, b, beta) == tuple(rational(row[k]) for k in ("la", "lb", "beta"))
        assert s >= row["eps_s_" + suffix] and t >= row["eps_t_" + suffix]
        if name == "B":
            assert Q("2.7182818286") ** beta.numerator < rate ** beta.denominator
    print(f"Theorem {name}: {count} intervals, endpoints and stored seed bounds verified.")


def log_bar(x):
    return sum(x**k / k for k in range(1, 5)) + x**5 / (1 - x)


def even_density_upper(c, side):
    eps = c["eps"]
    f = eps**2 / (2 * (1 - eps)**2)
    correction = (log_bar(eps) + log_bar(f)) / 4
    return (c["l_" + side] / 2 + c["beta"] * c["theta_" + side] / 2 + correction) / (c["beta"] - c["beta1"])


def verify_tension_row(c, row):
    assert tuple(c[k] for k in ("la", "lb", "beta", "beta1")) == tuple(
        rational(row[k]) for k in ("la", "lb", "beta", "beta1"))
    if "omega_a_low" in row:
        for side in ("a", "b"):
            assert c["omega_" + side] <= row["omega_" + side + "_low"]
            assert c["l_" + side] >= row["l1_" + side + "_up"]
            assert c["theta_" + side] >= row["theta_" + side + "_up"]
        assert c["eps"] >= row["eps_up"]
    else:
        for side in ("a", "b"):
            assert c["omega_" + side] <= row["omega_" + side]
            assert c["l_" + side] >= row["logZ1_" + side]
        assert c["theta_a"] >= row["theta2"]
        assert c["theta_b"] >= row["theta2"] - (c["lb"] - c["la"]) * row["w2"]
        assert c["eps"] >= row["eps"]


def verify_extension(cert, old_odd):
    folder = HERE / "extended"
    pattern = r"⟨([^,]+), ([^,]+), ([^,]+), \{ s := \[([^,]+),.*?t := \[([^,]+),.*?r := ([^,]+),"
    lean = (HERE / "ExtendedGap.lean").read_text(encoding="utf-8")
    table = [tuple(map(rational, row)) for row in re.findall(pattern, lean)]
    jobs = json.loads((folder / "tiling.json").read_text())
    assert len(table) == len(jobs) == 11 and table[0][0] == 12 and table[-1][1] == 16
    assert all(a[1] == b[0] for a, b in zip(table, table[1:]))
    for name, suffix in (("julia.jsonl", ""), ("python.jsonl", "_up")):
        rows = records(folder / name)
        for i, ((a, b, beta, s, t, rate), job, row) in enumerate(zip(table, jobs, rows, strict=True), 1):
            assert row["i"] == i and a < b
            assert all(row[k] == job[k] for k in ("la", "lb", "beta", "js2", "jt2", "c"))
            assert (a, b, beta) == tuple(Q(job[k]) for k in ("la", "lb", "beta"))
            assert (beta, job["js2"], job["jt2"], Q(job["c"])) == (Q(33, 20), 6, 5, 12)
            assert s - row["eps_s" + suffix] > Q(1,10**6)
            assert t - row["eps_t" + suffix] > Q(1,10**6)
            target = 1 if b <= Q(49,4) else Q("0.76") if b <= 14 else Q("0.46")
            power = beta * target
            assert Q("2.7182818286")**power.numerator < rate**power.denominator
    for language, suffix, index in (("julia", "", 1), ("python", "_up", 11)):
        [row] = records(folder / f"r2-even-last-{language}.jsonl")
        assert row["i"] == index
        assert all(row[key] == jobs[-1][key] for key in ("la", "lb", "beta", "js2", "jt2", "c"))
        assert row["eps_s" + suffix] <= table[-1][3] and row["eps_t" + suffix] <= table[-1][4]
    print("Revision spot checks: both stored enclosures on [15.5, 16] fit the final Lean row.")
    print("Extended even gap: both sets of 11 inputs fit the Lean chains throughout [12, 16].")

    odd = dict(old_odd)
    odd.update({24: Q("-26.800203"), 26: Q("-29.910943"), 28: Q("-33.172360"), 30: Q("-37.108380")})
    for name in ("odd-julia.jsonl", "odd-python.jsonl"):
        rows = [r for r in records(folder / name) if Q(r["x"]) <= 30]
        assert [Q(r["x"]) for r in rows] == [24, 26, 28, 30]
        for row in rows:
            assert row["two_j_star"] == 6 and row["penalty"] == 12
            assert Q(row["omega_lower"]) >= odd[int(row["x"])]
    baseline30 = odd[30]
    odd.update({30: Q("-36.161741"), 32: Q("-39.608918")})
    for penalty, points in ((16, [30,32]), (15, [32])):
        for language in ("python", "julia"):
            rows = records(folder / f"penalty{penalty}-{language}.jsonl")
            assert [Q(r["x"]) for r in rows] == points
            for row in rows:
                assert row["two_j_star"] == 6 and row["penalty"] == penalty
                x = int(row["x"])
                if penalty == 16 and x == 32:
                    assert -Q("40.000001") <= Q(row["omega_lower"]) <= -40
                else:
                    assert odd[x] <= Q(row["omega_lower"])
    for language in ("python", "julia"):
        [row] = records(folder / f"refined-{language}.jsonl")
        assert Q(row["x"]) == 32 and row["two_j_star"] == 6
        assert Q(row["penalty"]) == Q(15523, 1000)
        assert Q("-39.523661") <= Q(row["omega_lower"]) <= 40-64-Q(row["penalty"])
    odd[32] = Q("-39.523661")
    def trial(v, x):
        kinetic = Q(4,3) * sum(n*(n+2)*value**2 for n, value in enumerate(v))
        return (kinetic - x*sum(a*b for a, b in zip(v, v[1:]))) / sum(value**2 for value in v)
    bands = [(12, 16, [30,30,15,4,1], "0.42"), (16, 20, [30,32,18,6,1], "0.40"),
             (20, 24, [30,34,21,8,2], "0.36"), (24, 28, [30,36,23,10,3], "0.20"),
             (28, 30, [40,49,33,15,5,1], "0.20"), (30, 32, [40,50,34,16,5,1], "0.1425")]
    for a, b, v, floor in bands:
        assert all(odd[x]/2 - trial(v, x) >= Q(floor) for x in (a,b))
    assert Q("0.5584") + (Q("0.4910") - Q("0.5584"))/8 == Q("0.549975")
    assert trial([30,26,11,3], 12) == -Q(13520,2559)
    assert 1 + trial([30,26,11,3], 12) + cert[-1]["l_b"]/(2*cert[-1]["beta1"]) <= Q("1.05722")
    assert baseline30/2 - trial(bands[3][2], 30) < 0
    assert -20 - trial(bands[-1][2], 32) < 0
    assert trial(bands[-1][2],30) == -Q(152359,8307) and trial(bands[-1][2],32) == -Q(165346,8307)
    print("Winding trial: 12 endpoint checks through 32, the upper bound at 12 and secant at 12.25 passed.")


def main():
    if not __debug__:
        raise SystemExit("Run with ordinary Python so every assertion is checked.")
    a = json.loads((DATA / "replay/ladder_replay_results_regression.json").read_text(), parse_float=Q)
    verify_gap("A", [LEAN / "LadderIntervals.lean"], a["rows"], 6, 240)
    b = [row for letter in "AB" for row in records(DATA / f"zero_winding/even_replay_{letter}.jsonl")]
    verify_gap("B", [LEAN / f"LadderEven/Part{i}.lean" for i in range(1, 5)], b, 12, 760)

    fields = "la lb beta beta1 omega_a omega_b l_a l_b theta_a theta_b eps sigma".split()
    source = (LEAN / "TensionIntervals.lean").read_text(encoding="utf-8")
    entries = re.findall(r"^\s*⟨([0-9/(), \-]+)⟩(?:,|\])?\s*$", source, re.M)
    table = [tuple(map(rational, entry.split(","))) for entry in entries]
    check_tiling(table, 12)
    cert = [dict(zip(fields, row, strict=True)) for row in table]
    js = json.loads((DATA / "tension/tension_certificate.json").read_text())
    assert cert == [{k: Q(v) for k, v in row.items()} for row in js]
    py = [r for letter in "ABC" for r in records(DATA / f"tension/tension_replay_{letter}.jsonl")]
    jl = records(DATA / "tension/tension_seeds.jsonl")
    assert len(cert) == len(py) == len(jl) == 180
    for c, p, j in zip(cert, py, jl):
        assert 0 < c["beta1"] < c["beta"] and 0 <= c["eps"] < 1
        assert c["eps"]**2 / (2 * (1 - c["eps"])**2) <= Q(1, 2)
        for side in ("a", "b"):
            assert c["sigma"] <= c["omega_" + side] / 2 - even_density_upper(c, side)
        verify_tension_row(c, p)
        verify_tension_row(c, j)
    assert min(c["sigma"] for c in cert) == Q("0.5584")
    print("Theorem C: 180 intervals, both stored replays and both rational endpoint inequalities verified.")
    for row in records(HERE / "tension-180.jsonl"):
        assert row["i"] == 180
        verify_tension_row(cert[-1], row)
    assert len(records(HERE / "tension-180.jsonl")) == 1
    print("Archived numerical replay satisfies all seven input comparisons on [11.9, 12].")
    left = next(c for c in cert if c["lb"] == Q("11.3"))
    low = -left["l_b"] / (2 * left["beta1"])
    upper = even_density_upper(cert[-1], "b")
    slope = (upper - low) / (12 - left["lb"])
    assert low == -Q(29333221, 6000000) and upper <= -Q("5.33611")
    assert slope <= -Q("0.6389") and cert[-1]["sigma"] == Q("0.5584")
    end = Q("0.5584") - Q("0.3611") * Q("1.54")
    assert end == Q("0.002306")
    print(f"Secant slope <= {float(slope):.10f}; exact winding lower bound at 13.54: {end}.")
    odd = {12: cert[-1]["omega_b"], 14: Q("-12.245748"), 16: Q("-15.023872"),
           18: Q("-17.875510"), 20: Q("-20.791110"), 22: Q("-23.765594")}
    floors = {12: Q("0.5584"), 14: Q("0.4910"), 16: Q("0.3797"),
              18: Q("0.2317"), 20: Q("0.0517")}
    for name in ("odd-anchors.jsonl", "odd-julia.jsonl"):
        computed = records(HERE / name)
        assert [int(row["x"]) for row in computed] == [14, 16, 18, 20, 22]
        for row in computed:
            assert row["two_j_star"] == 6 and row["penalty"] == 12
            assert Q(row["omega_lower"]) >= odd[int(row["x"])]
    for x, floor in floors.items():
        assert odd[x] / 2 + Q("5.33611") + Q("0.6389") * (x-12) >= floor
    assert min(floors.values()) == Q("0.0517")
    assert odd[22] / 2 + Q("5.33611") + Q("0.6389") * 10 < 0
    print("Both stored odd-sector enclosure sets pass. Endpoint floors on [12, 20] are at least 517/10000.")
    # Independent counting for the worked odd-block example. On a two-cell
    # ring each rung satisfies the same two vertex triangle conditions.
    dim, first_omitted = 0, None
    for a, b, c, d in product(range(8), repeat=4):
        if (a+b) % 2 != 1 or (c+d) % 2 != 1:
            continue
        rungs = [r for r in range(8) if abs(a-c) <= r <= a+c and
                 abs(b-d) <= r <= b+d and (a+c+r) % 2 == (b+d+r) % 2 == 0]
        for r, s in product(rungs, repeat=2):
            labels = (a, b, c, d, r, s)
            if max(labels) <= 6:
                dim += 1
            else:
                energy = sum(n * (n+2) for n in labels)
                first_omitted = energy if first_omitted is None else min(first_omitted, energy)
    assert (dim, first_omitted) == (1734, 120)
    print("Independent label count: 1734 odd block states, first omitted numerator 120.")
    verify_extension(cert, odd)


if __name__ == "__main__":
    main()
