# tension_seeds.jl -- rigorous lower bounds on the string tension of the SU(2) ladder (Lemma 6 of the note).
# For an interval [la, lb] it returns sigma such that for every coupling in the interval, every flux cutoff >= the ones
# used (hence without cutoff) and every even L >= 2
#       E-(L) - E+(L) >= sigma L,
# with E+ / E- the lowest eigenvalue of H in the sector c = +1 / c = -1 of the winding charge. Ingredients:
#   omega  <= E-(2)                   (ground_lower in the odd sector: the operator inequality behind Lemma 3)
#   l1     >= log Z+(2, beta1)        (Lemma 3 in the even sector)
#   theta2 >= E+(2), slope w2         (trial vector on 2 plaquettes, even sector)
#   eps    >= 1 - Z+(4, beta) / Z+(2, beta)^2     (the spatial seed defect at temperature beta, as in Theorem B)
#   D = -(1/4) log(1 - eps) - (1/4) log(1 - eps^2 / (2 (1 - eps)^2))
#   sigma = omega / 2 - [ l1 / 2 + beta theta2 / 2 + D ] / (beta - beta1)
# evaluated at both endpoints (everything is affine or concave/convex in the right direction; see the note).
# usage: julia tension_seeds.jl tiling.json OUT.jsonl

using Printf, JSON3
include(joinpath(@__DIR__, "..", "replay", "ladder_replay.jl"))
prat(s) = (p = split(String(s), "/"); length(p) == 1 ? parse(Int, p[1]) // 1 : parse(Int, p[1]) // parse(Int, p[2]))

function Dfun(eps::IV)
    e1 = eps * eps / (interval(2.0) * (interval(1.0) - eps)^2)
    (up(eps) < 0.5 && up(e1) < 0.5) || error("seed defect too large for the recursion")
    -(log(interval(1.0) - eps) + log(interval(1.0) - e1)) / interval(4.0)
end

function run(tilingf, outp)
    jobs = JSON3.read(read(tilingf, String))
    done = isfile(outp) ? countlines(outp) : 0
    zc = Dict{Any,Any}(); tc = Dict{Any,Trial}(); cache = Dict{Any,Any}()
    io = open(outp, "a")
    for (i, job) in enumerate(jobs)
        i <= done && continue
        la, lb, beta, beta1, c = prat(job.la), prat(job.lb), prat(job.beta), prat(job.beta1), prat(job.c); js2, jt2 = Int(job.js2), Int(job.jt2)
        t0 = time()
        Ze = get!(() -> make_zup(js2, c; sector = :even)[1], zc, (js2, c, :even))
        Zo = get!(() -> make_zup(js2, c; sector = :odd)[1], zc, (js2, c, :odd))
        T4 = get!(() -> make_trial(jt2), tc, (4, jt2)); T2 = get!(() -> make_trial(js2 + 1; L = 2), tc, (2, js2 + 1))
        lz(b, lam) = get!(() -> log_zup(Ze, b, lam)[1], cache, (:lz, js2, b, lam))
        om(lam) = get!(() -> ground_lower(Zo, lam), cache, (:om, js2, lam))
        mid_ = (la + lb) / 2
        th4, w4, _ = theta_w(T4, la; sector = :even, lam_vec = mid_)
        th2, w2, _ = theta_w(T2, la; sector = :even, lam_vec = mid_)
        b = ri(beta); b1 = ri(beta1); d = ri(lb - la)
        # seed defect at temperature beta on the whole interval
        x0 = -(b * th4) - interval(2.0) * lz(beta, la); x1 = -(b * (th4 - d * w4)) - interval(2.0) * lz(beta, lb)
        eps = interval(nextfloat(1 - min(lo(exp(x0)), lo(exp(x1)))))
        lo(eps) > 0 || error("nonpositive defect")
        Dv = Dfun(eps)
        Ua = (lz(beta1, la) / interval(2.0) + b * th2 / interval(2.0) + Dv) / (b - b1)
        Ub = (lz(beta1, lb) / interval(2.0) + b * (th2 - d * w2) / interval(2.0) + Dv) / (b - b1)
        oa, ob = om(la), om(lb)
        sa = interval(oa) / interval(2.0) - Ua; sb = interval(ob) / interval(2.0) - Ub
        (isguaranteed(sa) && isguaranteed(sb)) || error("unguaranteed interval")
        sigma = prevfloat(min(lo(sa), lo(sb)))
        @printf(io, "{\"i\":%d,\"la\":\"%s\",\"lb\":\"%s\",\"beta\":\"%s\",\"beta1\":\"%s\",\"js2\":%d,\"jt2\":%d,\"c\":\"%s\",\"sigma\":%.12g,\"omega_a\":%.12g,\"omega_b\":%.12g,\"Eplus_per_plaq_up_a\":%.12g,\"Eplus_per_plaq_up_b\":%.12g,\"eps\":%.10g,\"D\":%.10g,\"theta2\":%.12g,\"w2\":%.12g,\"theta4\":%.12g,\"logZ1_a\":%.12g,\"logZ1_b\":%.12g}\n",
            i, job.la, job.lb, job.beta, job.beta1, js2, jt2, job.c, sigma, oa, ob, up(Ua), up(Ub), up(eps), up(Dv), up(th2), lo(w2), up(th4), up(lz(beta1, la)), up(lz(beta1, lb))); flush(io)
        @printf("%3d [%s, %s]: sigma >= %.6f   (E-(2)/2 >= %.6f, E+(L)/L <= %.6f, eps %.4g) (%.1fs)\n", i, job.la, job.lb, sigma, oa / 2, up(Ua), up(eps), time() - t0); flush(stdout)
        length(cache) > 40 && empty!(cache)
    end
    close(io)
end
run(ARGS[1], ARGS[2])
