# sector_bounds.jl -- EXPLORATION, not part of the claimed theorem.
# Rigorous (interval-arithmetic) seed defects for the zero-winding sector of the SU(2) ladder, by the same Lemma 3 /
# Lemma 4 machinery as replay/ladder_replay.jl with every sum restricted to the sector c = +1.
# What it would take to make this a theorem is in the note: one extra lemma (the sector penalty is an on-site,
# reflection-invariant, real diagonal term, so the penalised model is again a reflection-positive ring).
# usage: julia sector_bounds.jl OUT.json sector job [job ...]     job = la:lb:beta:js2:jt2:c   (rationals as a/b)

using Printf
include(joinpath(@__DIR__, "..", "replay", "ladder_replay.jl"))

prat(s) = (p = split(s, "/"); length(p) == 1 ? parse(Int, p[1]) // 1 : parse(Int, p[1]) // parse(Int, p[2]))

function run(outp, sector, jobs)
    zc = Dict{Any,Any}(); tc = Dict{Int,Trial}(); lc = Dict{Any,Any}(); recs = String[]
    for job in jobs
        f = split(job, ":"); la, lb, beta = prat(f[1]), prat(f[2]), prat(f[3]); js2, jt2 = parse(Int, f[4]), parse(Int, f[5]); c = prat(f[6])
        t0 = time()
        Z = get!(() -> make_zup(js2, c; sector = sector)[1], zc, (js2, c))
        T = get!(() -> make_trial(jt2), tc, jt2)
        la_ = get!(() -> log_zup(Z, beta, la), lc, (js2, c, beta, la)); lb_ = get!(() -> log_zup(Z, beta, lb), lc, (js2, c, beta, lb))
        th, w, e0 = theta_w(T, la; sector = sector)
        b = ri(beta); d = ri(lb - la)
        x0s = -(b * th) - interval(2.0) * la_[1]; x1s = -(b * (th - d * w)) - interval(2.0) * lb_[1]
        x0t = -(interval(2.0) * b * th) - interval(4.0) * la_[1]; x1t = -(interval(2.0) * b * (th - d * w)) - interval(4.0) * lb_[1]
        es = 1 - min(lo(exp(x0s)), lo(exp(x1s))); et = 1 - min(lo(exp(x0t)), lo(exp(x1t)))
        push!(recs, @sprintf("{\"la\":\"%s\",\"lb\":\"%s\",\"beta\":\"%s\",\"js2\":%d,\"jt2\":%d,\"c\":\"%s\",\"P_dim\":%d,\"eps_s\":%.12g,\"eps_t\":%.12g,\"theta\":%.12g,\"w\":%.12g,\"logZup_a\":%.12g,\"logZup_b\":%.12g,\"tail_rel_b\":%.3g}",
            f[1], f[2], f[3], js2, jt2, f[6], Z.nP, nextfloat(es), nextfloat(et), up(th), lo(w), up(la_[1]), up(lb_[1]), lb_[2]))
        @printf("[%s, %s] beta %s j* %d/2 c %s: eps_s %.6g eps_t %.6g tail/main %.1e (%.1fs)\n", f[1], f[2], f[3], js2, f[6], es, et, lb_[2], time() - t0); flush(stdout)
        open(fh -> print(fh, "[\n", join(recs, ",\n"), "\n]\n"), outp, "w")
    end
end
run(ARGS[1], Symbol(ARGS[2]), ARGS[3:end])
