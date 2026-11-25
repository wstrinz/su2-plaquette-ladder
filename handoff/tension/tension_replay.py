"""tension_replay.py -- second implementation for the string-tension theorem (Lemma 6 of the note).

For each interval of tiling.json it computes, with the Python machinery of ../zero_winding/even_replay.py (exact integer
matrix products, Arb balls, sympy 6j symbols, integer trial vectors), a number sigma such that for every coupling in the
interval, every flux cutoff >= the ones used and every even L >= 2
        E-(L) - E+(L) >= sigma L,
and the check stage compares it with the certified value in tension_certificate.json.

    omega  <= E-(2)                 ZUp(parity 1).ground_lower            (operator inequality behind Lemma 3)
    l1     >= log Z+(2, beta1)      ZUp(parity 0).log_upper                (Lemma 3)
    theta2 >= E+(2), slope w2       integer trial vector on 2 plaquettes
    eps    >= 1 - Z+(4, beta) / Z+(2, beta)^2                              (as in Theorem B, at temperature beta)
    D = -(1/4) log(1 - eps) - (1/4) log(1 - eps^2 / (2 (1 - eps)^2))
    sigma = omega / 2 - [ l1 / 2 + beta theta2 / 2 + D ] / (beta - beta1),  at both endpoints, the smaller one.

usage: tension_replay.py compute tiling.json OUT.jsonl first last
       tension_replay.py check-lean tension_certificate.json RESULT.json OUT.jsonl [OUT2.jsonl ...]
       (check-lean also accepts tension_seeds.jsonl, the Julia rows)
"""
import json, math, os, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "zero_winding"))
from fractions import Fraction as Fr
from flint import arb
from even_replay import ZUp, Trial, aq


def compute(tilingf, outp, first, last):
    til = json.load(open(tilingf)); last = min(last, len(til))
    done = {json.loads(l)["i"] for l in open(outp)} if os.path.exists(outp) else set()
    zc, tc, cache = {}, {}, {}; t00 = time.time(); fh = open(outp, "a")
    for i in range(first, last + 1):
        if i in done:
            continue
        cf = til[i - 1]; t0 = time.time()
        la, lb, beta, beta1, c, js2, jt2 = Fr(cf["la"]), Fr(cf["lb"]), Fr(cf["beta"]), Fr(cf["beta1"]), Fr(cf["c"]), cf["js2"], cf["jt2"]
        for par in (0, 1):
            if (js2, c, par) not in zc:
                zc[(js2, c, par)] = ZUp(js2, c, par); print(f"L=2 operators, parity {par}, j* = {js2}/2: P-dim {zc[(js2, c, par)].n}, dmin {zc[(js2, c, par)].dmin}", flush=True)
        if (4, jt2) not in tc:
            tc[(4, jt2)] = Trial(jt2); print(f"L=4 even-sector operators at cutoff {jt2}/2: dim {tc[(4, jt2)].n}", flush=True)
        if (2, js2 + 1) not in tc:
            tc[(2, js2 + 1)] = Trial(js2 + 1, L=2)
        Ze, Zo, T4, T2 = zc[(js2, c, 0)], zc[(js2, c, 1)], tc[(4, jt2)], tc[(2, js2 + 1)]
        def lz(b, lam):
            k = ("lz", js2, b, lam)
            if k not in cache: cache[k] = Ze.log_upper(b, lam)[0]
            return cache[k]
        def om(lam):
            k = ("om", js2, lam)
            if k not in cache: cache[k] = Zo.ground_lower(lam)
            return cache[k]
        mid = (la + lb) / 2
        th4, w4 = T4.theta_w(la, mid); th2, w2 = T2.theta_w(la, mid)
        b, b1, d = aq(beta), aq(beta1), aq(lb - la)
        x0 = -(b * th4) - 2 * lz(beta, la); x1 = -(b * (th4 - d * w4)) - 2 * lz(beta, lb)
        e0, e1_ = (1 - x0.exp()).upper(), (1 - x1.exp()).upper()
        eps = arb(e0 if e0 > e1_ else e1_)
        assert eps > 0 and eps < arb(1) / 2
        eps1 = eps * eps / (2 * (1 - eps) ** 2)
        assert eps1 < arb(1) / 2
        Dv = -((1 - eps).log() + (1 - eps1).log()) / 4
        Ua = (lz(beta1, la) / 2 + b * th2 / 2 + Dv) / (b - b1)
        Ub = (lz(beta1, lb) / 2 + b * (th2 - d * w2) / 2 + Dv) / (b - b1)
        sa, sb = om(la) / 2 - Ua, om(lb) / 2 - Ub
        lowf = lambda x: math.nextafter(float(x.lower()), -math.inf)
        sigma = min(lowf(sa), lowf(sb))
        upf = lambda x: math.nextafter(float(x.upper()), math.inf)
        # the four inputs of Lemma 6 at the two endpoints, rounded in the safe direction (for the check against the Lean certificate)
        fh.write(json.dumps(dict(i=i, la=cf["la"], lb=cf["lb"], beta=cf["beta"], beta1=cf["beta1"], js2=js2, jt2=jt2, sigma_low=sigma,
                                 omega_a_low=lowf(om(la)), omega_b_low=lowf(om(lb)), l1_a_up=upf(lz(beta1, la)), l1_b_up=upf(lz(beta1, lb)),
                                 theta_a_up=upf(th2), theta_b_up=upf(th2 - d * w2), eps_up=upf(eps),
                                 omega_a=float(om(la).mid()), omega_b=float(om(lb).mid()), Eplus_up_a=float(Ua.upper()), Eplus_up_b=float(Ub.upper()),
                                 eps=float(eps.upper()), theta2=float(th2.mid()), theta4=float(th4.mid()))) + "\n"); fh.flush()
        print(f"{i:3d} [{la}, {lb}]: sigma >= {sigma:.6f}   (E-(2)/2 >= {float(om(la).mid()) / 2:.6f}, E+(L)/L <= {float(Ua.upper()):.6f}, eps {float(eps.upper()):.4g}) ({time.time() - t0:.1f}s)", flush=True)
        if len(cache) > 40:
            cache.clear()
    print(f"done {first}..{last}, {time.time() - t00:.0f}s", flush=True)


def check(certf, outp, files):
    cert = json.load(open(certf)); rows = {}
    for f in files:
        for l in open(f):
            r = json.loads(l); r.setdefault("sigma_low", r.get("sigma")); rows[(Fr(r["la"]), Fr(r["lb"]))] = r
    assert Fr(cert[0]["la"]) == 0 and all(Fr(a["lb"]) == Fr(b["la"]) for a, b in zip(cert, cert[1:]))
    res = []; npass = 0
    for cv in cert:
        r = rows.get((Fr(cv["la"]), Fr(cv["lb"])))
        ok = r is not None and Fr(r["sigma_low"]) >= Fr(cv["sigma"])
        npass += ok
        res.append(dict(la=cv["la"], lb=cv["lb"], sigma_cert=cv["sigma"], sigma_replay=None if r is None else r["sigma_low"], ok=bool(ok)))
    sl = [x["sigma_replay"] - float(Fr(x["sigma_cert"])) for x in res if x["sigma_replay"] is not None]
    summary = dict(intervals=len(cert), last_coupling=cert[-1]["lb"], passed=npass, smallest_margin=min(sl) if sl else None)
    json.dump(dict(summary=summary, rows=res), open(outp, "w")); print(summary)
    for x in res:
        if not x["ok"]: print("FAIL", x)


def logbar(x):
    """Rational upper bound on -log(1 - x), 0 <= x < 1 (the one used in the Lean file)."""
    return x + x**2 / 2 + x**3 / 3 + x**4 / 4 + x**5 / (1 - x)


def check_lean(certf, outp, files):
    """Check the hypotheses of `tension_on_interval` for every entry of the Lean certificate: the eight endpoint
    bounds (omega from below, l and theta from above), the defect bound, and -- redundantly with the Lean kernel --
    the rational arithmetic sigma <= bound of Lemma 6 at both endpoints. Works for rows of this script and for the
    rows of tension_seeds.jl (Julia), which carry the same quantities under other names."""
    cert = json.load(open(certf)); rows = {}
    for f in files:
        for l in open(f):
            r = json.loads(l)
            if "omega_a_low" not in r:      # Julia row: omega_a, omega_b are lower bounds; logZ1, theta2, eps upper bounds; w2 a lower bound
                d = float(Fr(r["lb"]) - Fr(r["la"]))
                r = dict(r, omega_a_low=r["omega_a"], omega_b_low=r["omega_b"], l1_a_up=r["logZ1_a"], l1_b_up=r["logZ1_b"],
                         theta_a_up=r["theta2"], theta_b_up=math.nextafter(r["theta2"] - d * r["w2"], math.inf) + 1e-12, eps_up=r["eps"])
            rows[(Fr(r["la"]), Fr(r["lb"]))] = r
    assert Fr(cert[0]["la"]) == 0 and all(Fr(a["lb"]) == Fr(b["la"]) for a, b in zip(cert, cert[1:]))
    res = []; npass = 0; marg = {}
    for cv in cert:
        r = rows.get((Fr(cv["la"]), Fr(cv["lb"]))); c = {k: Fr(v) for k, v in cv.items()}
        f = c["eps"] ** 2 / (2 * (1 - c["eps"]) ** 2)
        sg = lambda om, l, th: om / 2 - (l / 2 + c["beta"] * th / 2 + (logbar(c["eps"]) + logbar(f)) / 4) / (c["beta"] - c["beta1"])
        arith = 0 < c["beta1"] < c["beta"] and 0 <= c["eps"] < 1 and f <= Fr(1, 2) and c["sigma"] <= sg(c["omega_a"], c["l_a"], c["theta_a"]) and c["sigma"] <= sg(c["omega_b"], c["l_b"], c["theta_b"])
        m = None
        if r is not None and Fr(r["beta"]) == c["beta"] and Fr(r["beta1"]) == c["beta1"]:
            m = dict(omega_a=Fr(r["omega_a_low"]) - c["omega_a"], omega_b=Fr(r["omega_b_low"]) - c["omega_b"],
                     l_a=c["l_a"] - Fr(r["l1_a_up"]), l_b=c["l_b"] - Fr(r["l1_b_up"]),
                     theta_a=c["theta_a"] - Fr(r["theta_a_up"]), theta_b=c["theta_b"] - Fr(r["theta_b_up"]), eps=c["eps"] - Fr(r["eps_up"]))
            for k, v in m.items(): marg[k] = min(marg.get(k, 1e9), float(v))
        ok = bool(arith and m is not None and all(v >= 0 for v in m.values())); npass += ok
        res.append(dict(la=cv["la"], lb=cv["lb"], sigma=cv["sigma"], arithmetic_ok=bool(arith), ok=ok, margins=None if m is None else {k: float(v) for k, v in m.items()}))
    summary = dict(intervals=len(cert), last_coupling=cert[-1]["lb"], passed=npass, smallest_margins=marg,
                   min_sigma=float(min(Fr(c["sigma"]) for c in cert)))
    json.dump(dict(summary=summary, rows=res), open(outp, "w")); print(summary)
    for x in res:
        if not x["ok"]: print("FAIL", x)


if __name__ == "__main__":
    if sys.argv[1] == "compute":
        compute(sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]))
    elif sys.argv[1] == "check-lean":
        check_lean(sys.argv[2], sys.argv[3], sys.argv[4:])
    else:
        check(sys.argv[2], sys.argv[3], sys.argv[4:])
