# gap_scan.jl -- floating-point exploration, NOT part of any certificate.
# Lowest levels of the SU(2) ladder H = (1/3) diag4 - lam W at a flux cutoff, resolved by the Z2 winding charge
#   c = (-1)^(2 j_b + 2 j_t)  (the same at every rung by the Gauss law; tr U_p changes b and t together, so c is conserved).
# c = +1 holds the ground state and the plaquette ("glueball") excitations, c = -1 the states with odd flux winding
# around the ring ("torelons").
# usage: julia gap_scan.jl OUT.json L J2 lam_from lam_step lam_to [spectrum]
#   with the last argument "spectrum" the full spectrum is written too (dense; small cases only).

using KrylovKit, Printf, Random
include(joinpath(@__DIR__, "..", "replay", "ladder_ops.jl"))

function lowest(H, k, v0)
    n = size(H, 1)
    if n <= 2500
        return eigvals(Symmetric(Matrix(H)))[1:min(k, n)], v0
    end
    vals, vecs, info = eigsolve(H, v0, k, :SR; ishermitian = true, tol = 1e-10, krylovdim = max(30, 2k + 12), maxiter = 600)
    info.converged >= k || @warn "not converged" info.converged
    real.(vals[1:k]), vecs[1]
end

function main()
    outp = ARGS[1]; L = parse(Int, ARGS[2]); J2 = parse(Int, ARGS[3])
    lams = parse(Float64, ARGS[4]):parse(Float64, ARGS[5]):parse(Float64, ARGS[6])
    full = length(ARGS) >= 7 && ARGS[7] == "spectrum"
    t0 = time(); o = build_ops(L, J2); n = length(o.basis)
    W = sparse(o.rows, o.cols, o.ampF[o.ks], n, n); W = (W + W') / 2
    D = spdiagm(0 => o.diag4 ./ 3)
    even = findall(st -> iseven(st[1] + st[2]), o.basis); odd = findall(st -> isodd(st[1] + st[2]), o.basis)
    @printf("L=%d cutoff %d/2: dim %d (even %d, odd %d), built in %.0fs\n", L, J2, n, length(even), length(odd), time() - t0); flush(stdout)
    We = W[even, even]; Wo = W[odd, odd]; De = D[even, even]; Do = D[odd, odd]
    o = nothing; W = nothing; GC.gc()
    rng = MersenneTwister(5); ve = randn(rng, length(even)); vo = randn(rng, length(odd))
    recs = String[]
    for lam in lams
        t1 = time()
        ee, ve = lowest(De - lam .* We, 4, ve)
        eo, vo = lowest(Do - lam .* Wo, 2, vo)
        spec = ""
        if full
            se = eigvals(Symmetric(Matrix(De - lam .* We))); sp = sort(vcat(se, eigvals(Symmetric(Matrix(Do - lam .* Wo)))))
            spec = ",\"spectrum\":[" * join((@sprintf("%.12g", x) for x in sp), ",") * "],\"spectrum_even\":[" * join((@sprintf("%.12g", x) for x in se), ",") * "]"
        end
        push!(recs, @sprintf("{\"L\":%d,\"J2\":%d,\"lam\":%.4f,\"E0\":%.12f,\"even\":[%s],\"odd\":[%s]%s}", L, J2, lam, ee[1],
            join((@sprintf("%.10f", x - ee[1]) for x in ee[2:end]), ","), join((@sprintf("%.10f", x - ee[1]) for x in eo), ","), spec))
        @printf("lam %.2f  E0 %.8f  even gaps %s  odd gaps %s  (%.1fs)\n", lam, ee[1], join((@sprintf("%.5f", x - ee[1]) for x in ee[2:end]), " "),
            join((@sprintf("%.5f", x - ee[1]) for x in eo), " "), time() - t1); flush(stdout)
        open(f -> print(f, "[\n", join(recs, ",\n"), "\n]\n"), outp, "w")
    end
end
main()
