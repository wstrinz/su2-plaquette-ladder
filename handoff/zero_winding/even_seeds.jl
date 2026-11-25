# even_seeds.jl -- seed defects for the zero-winding sector (c = +1) of the SU(2) ladder on the intervals of tiling.json.
# Interval arithmetic throughout (the machinery of ../replay/ladder_replay.jl with every sum restricted to the sector).
# For interval [la, lb] and inverse temperature beta the two numbers eps_s, eps_t written out satisfy, for every coupling
# in the interval and every flux cutoff >= the ones used,
#     1 - eps_s <= Z+(4, beta) / Z+(2, beta)^2,       1 - eps_t <= Z+(4, 2 beta) / Z+(4, beta)^2,
# with Z+ the partition function of the sector (the second uses Z+(4) <= Z+(2)^2, a moment inequality of the sector).
# usage: julia even_seeds.jl tiling.json OUT.jsonl      (resumes if OUT exists)

using Printf, JSON3
include(joinpath(@__DIR__, "..", "replay", "ladder_replay.jl"))
prat(s) = (p = split(String(s), "/"); length(p) == 1 ? parse(Int, p[1]) // 1 : parse(Int, p[1]) // parse(Int, p[2]))

function run(tilingf, outp)
    jobs = JSON3.read(read(tilingf, String))
    done = isfile(outp) ? countlines(outp) : 0
    zc = Dict{Any,Any}(); tc = Dict{Int,Trial}(); lc = Dict{Any,Any}()
    io = open(outp, "a")
    for (i, job) in enumerate(jobs)
        i <= done && continue
        la, lb, beta, c = prat(job.la), prat(job.lb), prat(job.beta), prat(job.c); js2, jt2 = Int(job.js2), Int(job.jt2)
        t0 = time()
        Z = get!(() -> make_zup(js2, c; sector = :even)[1], zc, (js2, c))
        T = get!(() -> make_trial(jt2), tc, jt2)
        la_ = get!(() -> log_zup(Z, beta, la), lc, (js2, c, beta, la)); lb_ = get!(() -> log_zup(Z, beta, lb), lc, (js2, c, beta, lb))
        th, w, e0 = theta_w(T, la; sector = :even, lam_vec = (la + lb) / 2)      # trial vector from the midpoint coupling
        b = ri(beta); d = ri(lb - la)
        x0s = -(b * th) - interval(2.0) * la_[1]; x1s = -(b * (th - d * w)) - interval(2.0) * lb_[1]
        x0t = -(interval(2.0) * b * th) - interval(4.0) * la_[1]; x1t = -(interval(2.0) * b * (th - d * w)) - interval(4.0) * lb_[1]
        es = nextfloat(1 - min(lo(exp(x0s)), lo(exp(x1s)))); et = nextfloat(1 - min(lo(exp(x0t)), lo(exp(x1t))))
        @printf(io, "{\"i\":%d,\"la\":\"%s\",\"lb\":\"%s\",\"beta\":\"%s\",\"js2\":%d,\"jt2\":%d,\"c\":\"%s\",\"P_dim\":%d,\"eps_s\":%.12g,\"eps_t\":%.12g,\"theta\":%.14g,\"w\":%.14g,\"logZup_a\":%.14g,\"logZup_b\":%.14g,\"tail_rel_b\":%.3g}\n",
            i, job.la, job.lb, job.beta, js2, jt2, job.c, Z.nP, es, et, up(th), lo(w), up(la_[1]), up(lb_[1]), lb_[2]); flush(io)
        @printf("%3d [%s, %s] beta %s: eps_s %.6g eps_t %.6g tail/main %.1e (%.1fs)\n", i, job.la, job.lb, job.beta, es, et, lb_[2], time() - t0); flush(stdout)
        length(lc) > 6 && (delete!(lc, first(keys(lc))))
    end
    close(io)
end
run(ARGS[1], ARGS[2])
