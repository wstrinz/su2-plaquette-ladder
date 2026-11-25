# ising_map_test.jl -- literature anchor for the plaquette matrix elements at the lowest cutoff.
#
# X. Yao, arXiv:2303.14264, eq. (11): at flux cutoff 1/2 the periodic SU(2) plaquette chain is the spin chain
#     H = (3/2) g^2 sum n_i - (3/4) g^2 sum n_i n_{i+1} - (2 / (a^2 g^2)) sum f(n_{i-1}) f(n_{i+1}) sigma^x_i,
# n_i in {0, 1} (plaquette i carries a loop of flux 1/2), f(0) = 1, f(1) = -1/2; tr U_p acts as f f sigma^x.
# In the units of the note (one unit of fundamental flux on a link costs 1, i.e. g^2 / 2 = 4/3):
#     H = sum (4 n_i - 2 n_i n_{i+1}) - (lambda / 2) sum f(n_{i-1}) f(n_{i+1}) sigma^x_i.
# The test builds H = (1/3) diag4 - lambda W from ladder_ops.jl at cutoff 1/2, restricted to the sector c = +1,
# and compares its spectrum with that of the spin chain. The two conventions for the sign of f(1) are related by a
# diagonal change of basis on a ring, so this test sees the electric normalisation and the magnitudes 1, 1/2, 1/4 of the
# plaquette amplitudes, not their signs (the commutator test is the sign-sensitive one).
#
# usage: julia ising_map_test.jl OUT.json
include(joinpath(@__DIR__, "ladder_ops.jl"))
using LinearAlgebra, Printf

function ladder_spectrum(L, lam)
    o = build_ops(L, 1)
    keep = [i for (i, st) in enumerate(o.basis) if iseven(Int(st[1]) + Int(st[2]))]
    pos = Dict(i => k for (k, i) in enumerate(keep)); n = length(keep)
    H = zeros(n, n)
    for (k, i) in enumerate(keep); H[k, k] = o.diag4[i] / 3; end
    for e in eachindex(o.rows)
        r, c = Int(o.rows[e]), Int(o.cols[e])
        (haskey(pos, r) && haskey(pos, c)) || continue
        H[pos[r], pos[c]] -= lam * o.ampF[o.ks[e]]
    end
    @assert norm(H - H') < 1e-12
    n, eigvals(Symmetric(H))
end

function ising_spectrum(L, lam; f1 = -0.5)
    n = 2^L; H = zeros(n, n); f(s) = s == 0 ? 1.0 : f1
    bit(c, x) = (c >> mod(x, L)) & 1
    for c in 0:n-1
        H[c+1, c+1] = sum(4 * bit(c, x) - 2 * bit(c, x) * bit(c, x + 1) for x in 0:L-1)
        for x in 0:L-1
            d = xor(c, 1 << x)
            H[d+1, c+1] -= (lam / 2) * f(bit(c, x - 1)) * f(bit(c, x + 1))
        end
    end
    eigvals(Symmetric(H))
end

function main()
    out = String[]; worst = 0.0; worst_ctrl = Inf
    for L in 2:8, lam in (0.5, 2.0, 6.0, 12.0)
        n, a = ladder_spectrum(L, lam); b = ising_spectrum(L, lam)
        @assert n == 2^L
        d = maximum(abs.(a .- b)); worst = max(worst, d)
        # control: the same chain with the neighbour factor 1/2 replaced by 0.45 must NOT match
        dc = maximum(abs.(a .- ising_spectrum(L, lam; f1 = -0.45))); worst_ctrl = min(worst_ctrl, dc)
        @printf("L=%d lambda=%4.1f  dim %3d  max |spectrum difference| %.2e   control %.2e\n", L, lam, n, d, dc)
        push!(out, @sprintf("{\"L\":%d,\"lambda\":%.1f,\"dim\":%d,\"max_diff\":%.3e,\"control_diff\":%.3e}", L, lam, n, d, dc))
    end
    open(ARGS[1], "w") do io
        print(io, "{\"source\":\"arXiv:2303.14264 eq. (11)\",\"cutoff\":\"1/2\",\"sector\":\"c=+1\",\"worst_diff\":", @sprintf("%.3e", worst), ",\"smallest_control_diff\":", @sprintf("%.3e", worst_ctrl), ",\"cases\":[", join(out, ","), "]}")
    end
    println("worst difference ", worst, "; smallest control difference ", worst_ctrl)
end
main()
