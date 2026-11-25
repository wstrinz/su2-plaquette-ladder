# published_formula_test.jl -- the operator tables of ladder_ops.jl against a literal evaluation of a published formula.
#
# X. Yao, arXiv:2303.14264, supplemental material (the display after eq. (33); cited there to Klco, Stryker and Savage 2020
# and ARahman, Lewis, Mendicelli and Powell 2021), for a plaquette with loop links 1..4 and external links a..d,
# a between links 1 and 2, b between 2 and 3, c between 3 and 4, d between 4 and 1:
#   <J1 J2 J3 J4| tr U |j1 j2 j3 j4> = prod_beta (-1)^(j_beta) prod_alpha [ (-1)^(j_alpha + J_alpha) sqrt((2 j_alpha + 1)(2 J_alpha + 1)) ]
#        {ja j1 j2; 1/2 J2 J1} {jb j2 j3; 1/2 J3 J2} {jc j3 j4; 1/2 J4 J3} {jd j4 j1; 1/2 J1 J4}.
# Here it is evaluated in one piece (one overall sign, one overall square) for every local configuration that occurs in the
# operator tables, and compared exactly (sign, and square as a rational number) with the product of four corner factors that
# ladder_ops.jl uses. Agreement shows that the corner formula of the note is this published formula; it does not show that the
# published formula is right (the commutator, orthonormality and spectral tests are about that).
#
# usage: julia published_formula_test.jl OUT.json L:J2 [L:J2 ...]
include(joinpath(@__DIR__, "ladder_ops.jl"))
using Printf

function published(key)
    b, t, r, rp, abp, atp, abn, atn, db, dt, dr, drp = key
    j = (r, b, rp, t); J = (r + dr, b + db, rp + drp, t + dt); ext = (abp, abn, atn, atp)     # loop r -> b -> r' -> t
    e2 = sum(ext) + sum(j) + sum(J)                       # doubled exponent of (-1)
    iseven(e2) || error("non-integer exponent")
    sg = iseven(e2 ÷ 2) ? 1 : -1; sq = big(1) // 1
    for k in 1:4
        k2 = k == 4 ? 1 : k + 1
        q, rr = sixj(ext[k], j[k], j[k2], 1, J[k2], J[k])
        q == 0 && return (0, big(0) // 1)
        sg *= Int(sign(q)); sq *= q^2 * rr * (j[k] + 1) * (J[k] + 1)
    end
    (sg, sq)
end

function main()
    out = String[]
    for spec in ARGS[2:end]
        L, J2 = parse.(Int, split(spec, ":"))
        o = build_ops(L, J2); seen = Dict{Int32,Int32}()
        for e in eachindex(o.kid); seen[o.kid[e]] = o.ks[e]; end
        nbad = 0
        for (kid, k) in seen
            sg, sq4 = o.amps[k]                          # entry of W = tr U / 2: (sign, square)
            psg, psq = published(o.keys[kid])
            (sg == psg && 4 * sq4 == psq) || (nbad += 1)
        end
        @printf("L=%d cutoff %d/2: %d local configurations, %d disagree\n", L, J2, length(seen), nbad)
        push!(out, @sprintf("{\"L\":%d,\"cutoff2\":%d,\"configurations\":%d,\"disagree\":%d}", L, J2, length(seen), nbad))
    end
    # control: with the corner sign rule of ladder_ops.jl switched off, the tables must disagree with the published formula
    PHASE_RULE[] = false
    o = build_ops(3, 3); seen = Dict{Int32,Int32}()
    for e in eachindex(o.kid); seen[o.kid[e]] = o.ks[e]; end
    nbad = count(((kid, k),) -> o.amps[k] != (published(o.keys[kid])[1], published(o.keys[kid])[2] / 4), collect(seen))
    PHASE_RULE[] = true
    @printf("control (corner sign rule off, L=3 cutoff 3/2): %d of %d disagree\n", nbad, length(seen))
    open(ARGS[1], "w") do io
        print(io, "{\"source\":\"arXiv:2303.14264 supplemental material, plaquette matrix element\",\"comparison\":\"exact: sign and rational square\",\"runs\":[", join(out, ","), "],\"control_sign_rule_off\":{\"L\":3,\"cutoff2\":3,\"configurations\":", length(seen), ",\"disagree\":", nbad, "}}")
    end
end
main()
