# sector_moment_check.jl -- falsification test for the sector lemma (exploration).
# If the winding-sector penalty is an on-site reflection-invariant real term (the candidate Lemma 5), then the
# partition functions of each winding sector separately obey the three moment inequalities of the purity criterion:
#   sq_le:    Z_2n <= Z_n^2          squaring: 2 (Z_2n^2 - Z_4n) <= (Z_n^2 - Z_2n)^2          le_rpow: Z_q <= Z_p^(q/p), even p <= q
# Tested for the even sector (c = +1), the odd sector (c = -1), and, as a quantity for which nothing is claimed,
# the twisted trace Z_even - Z_odd.
# usage: julia sector_moment_check.jl OUT.json

using Printf
include(joinpath(@__DIR__, "..", "replay", "ladder_ops.jl"))
setprecision(BigFloat, 200)

function sector_spectra(L, J2, lam)
    o = build_ops(L, J2); n = length(o.basis)
    H = spdiagm(0 => o.diag4 ./ 3) - lam .* sparse(o.rows, o.cols, o.ampF[o.ks], n, n)
    ev = findall(st -> iseven(st[1] + st[2]), o.basis); od = findall(st -> isodd(st[1] + st[2]), o.basis)
    eigvals(Symmetric(Matrix(H[ev, ev]))), eigvals(Symmetric(Matrix(H[od, od])))
end

Zsum(spec, beta) = sum(exp(-big(beta) * big(x)) for x in spec)

function check(Z, Ls)          # Z: Dict L => BigFloat; returns the largest violations (<= 0 means the inequality holds)
    sq = maximum(Float64(log(Z[2n]) - 2 * log(Z[n])) for n in Ls if haskey(Z, 2n); init = -Inf)
    sqz = maximum(Float64((2 * (Z[2n]^2 - Z[4n]) - (Z[n]^2 - Z[2n])^2) / Z[n]^4) for n in Ls if haskey(Z, 4n); init = -Inf)
    rp = maximum(Float64(log(Z[q]) - big(q) / p * log(Z[p])) for p in Ls for q in Ls if p < q; init = -Inf)
    (sq, sqz, rp)
end

recs = String[]; allok = Dict("even" => true, "odd" => true, "twisted" => true)
for (J2, Ls) in ((1, (2, 4, 6, 8, 10, 12)), (2, (2, 4, 6)))
    for lam in (0.5, 2.0, 6.0)
        spec = Dict(L => sector_spectra(L, J2, lam) for L in Ls)
        for beta in (0.2, 1.0, 3.0)
            Ze = Dict(L => Zsum(spec[L][1], beta) for L in Ls); Zo = Dict(L => Zsum(spec[L][2], beta) for L in Ls)
            Zt = Dict(L => Ze[L] - Zo[L] for L in Ls)
            for (name, Z) in (("even", Ze), ("odd", Zo), ("twisted", Zt))
                all(v -> v > 0, values(Z)) || (push!(recs, @sprintf("{\"J\":%.1f,\"lam\":%.1f,\"beta\":%.1f,\"which\":\"%s\",\"ok\":false,\"note\":\"non-positive\"}", J2 / 2, lam, beta, name)); allok[name] = false; continue)
                sq, sqz, rp = check(Z, Ls); ok = max(sq, sqz, rp) <= 1e-12
                allok[name] &= ok
                push!(recs, @sprintf("{\"J\":%.1f,\"lam\":%.1f,\"beta\":%.1f,\"which\":\"%s\",\"ok\":%s,\"sq_le\":%.3e,\"squaring\":%.3e,\"le_rpow\":%.3e}", J2 / 2, lam, beta, name, ok, sq, sqz, rp))
            end
        end
        @printf("cutoff %d/2 lam %.1f done: %s\n", J2, lam, allok); flush(stdout)
        open(f -> print(f, "[\n", join(recs, ",\n"), "\n]\n"), ARGS[1], "w")
    end
end
println("all hold: ", allok, "   cases per sector: ", length(recs) ÷ 3)
