# peter_weyl_test.jl -- a test of the plaquette matrix elements that uses no 6j symbol in its target values.
#
# Facts used (Haar measure and Schur orthogonality only). On the periodic ladder let B be the holonomy once around
# the ring along the bottom legs and U_p the plaquette holonomies. Each U_p contains a top leg t_p that occurs in no
# other of these loops, so (B, U_1, ..., U_L) are independent Haar-distributed, and therefore the functions
#       u(jB; j_1, ..., j_L) = chi_jB(B) prod_p chi_{j_p}(U_p)
# are orthonormal. chi_jB(B) applied to the constant function is a single spin-network state (bottom legs jB, all
# else 0), and chi_j(U_p) = U_{2j}(tr U_p / 2) with U_n the Chebyshev polynomial of the second kind. So, building
# the u's from the operators W_p = tr U_p / 2 of ladder_ops.jl,
#   (1) their Gram matrix must be the identity;
#   (2) for a single excited plaquette, the weight of u on bottom-leg label k must be (2k+1) / ((2jB+1)(2j+1)).
# The labels of u are bounded by jB + j_p on bottom legs and j_p + j_{p+1} on rungs, so with those sums within the
# cutoff nothing is truncated. The same test with top and bottom exchanged covers the mirror corners.
# This test sees the magnitudes of the matrix elements and is blind to their signs (the control with the corner sign
# rule removed passes it); the sign-sensitive companion is commutator_test.jl. Control: one local configuration
# rescaled by 1.05.
#
# usage: julia peter_weyl_test.jl OUT.json L:J2:Jc:nsample [...]

using Printf, Random
include(joinpath(@__DIR__, "ladder_ops.jl"))

function plaquette_mats(o::Ops, vals)          # vals: one value per entry
    n = length(o.basis)
    [sparse(o.rows[o.plaq.==p], o.cols[o.plaq.==p], vals[o.plaq.==p], n, n) for p in 1:o.L]
end

function tuples(L, J2)
    out = Vector{Vector{Int}}()
    function rec(p, cur)
        if p > L
            (L == 1 || cur[end] + cur[2] <= J2) && push!(out, copy(cur))
            return
        end
        for j in 0:J2
            cur[1] + j <= J2 || continue
            (p > 1 && cur[end] + j > J2) && continue
            push!(cur, j); rec(p + 1, cur); pop!(cur)
        end
    end
    for jB in 0:J2
        rec(1, [jB])
    end
    out
end

"""Vectors u(jB; j_1..j_L) for all admissible tuples; `side` = :bottom or :top chooses which legs carry the ring loop."""
function character_vectors(o::Ops, W, side)
    n = length(o.basis); L = o.L; J2 = o.J2
    off = side == :bottom ? 2 : 1                  # position of the leg inside (b, t, r), counted from the end: 3x-2 or 3x-1
    idx = Dict{Vector{Int8},Int}(st => i for (i, st) in enumerate(o.basis))
    tl = tuples(L, J2)
    U = zeros(n, length(tl))
    cache = Dict{Vector{Int},Vector{Float64}}()
    function vec_for(t)          # t = (jB, j_1, ..., j_m), m <= L: plaquettes beyond m are unexcited
        get!(cache, copy(t)) do
            if length(t) == 1
                st = zeros(Int8, 3L)
                for x in 1:L
                    st[3x-off] = t[1]
                end
                v = zeros(n); v[idx[st]] = 1.0
                return v
            end
            p = length(t) - 1; j = t[end]
            base = vec_for(t[1:end-1])
            j == 0 && return base
            um = base; u = 2 .* (W[p] * base)                      # U_0, U_1
            for _ in 2:j
                um, u = u, 2 .* (W[p] * u) .- um
            end
            u
        end
    end
    for (c, t) in enumerate(tl)
        U[:, c] = vec_for(t)
    end
    tl, U
end

function run_case(L, J2, Jc, ns)
    o = build_ops(L, J2); vals = o.ampF[o.ks]
    res = Dict{String,Any}("L" => L, "J2" => J2, "dim" => length(o.basis))
    W = plaquette_mats(o, vals)
    for side in (:bottom, :top)
        tl, U = character_vectors(o, W, side)
        G = U' * U
        res["n_vectors"] = length(tl)
        res["gram_dev_$(side)"] = maximum(abs, G - I)
        # (2): single excited plaquette (plaquette 1) over a ring loop
        leg = side == :bottom ? 1 : 2                  # label index of b_1 or t_1
        wdev = 0.0; nw = 0
        for (c, t) in enumerate(tl)
            (t[2] > 0 && all(==(0), t[3:end])) || continue
            jB, j = t[1], t[2]
            wt = Dict{Int,Float64}()
            for (i, st) in enumerate(o.basis)
                U[i, c] == 0 && continue
                wt[Int(st[leg])] = get(wt, Int(st[leg]), 0.0) + U[i, c]^2
            end
            for k in abs(jB - j):2:(jB+j)
                wdev = max(wdev, abs(get(wt, k, 0.0) - (k + 1) / ((jB + 1) * (j + 1)))); nw += 1
            end
        end
        res["weight_dev_$(side)"] = wdev; res["n_weights"] = nw
    end
    # control: this test sees magnitudes, not signs. Rescale one local configuration (8 labels and a move, with the
    # reverse move) by 1.05, for a random sample of configurations with labels within Jc, and count detections.
    keyidx = Dict(k => i for (i, k) in enumerate(o.keys))
    relevant = [i for (i, k) in enumerate(o.keys) if maximum(k[1:8]) <= Jc && max(k[1] + k[9], k[2] + k[10], k[3] + k[11], k[4] + k[12]) <= Jc]
    rng = MersenneTwister(7); det = 0; tried = 0
    for i in shuffle(rng, relevant)[1:min(ns, length(relevant))]
        k = o.keys[i]
        rev = (k[1] + k[9], k[2] + k[10], k[3] + k[11], k[4] + k[12], k[5], k[6], k[7], k[8], -k[9], -k[10], -k[11], -k[12])
        j = get(keyidx, rev, 0); j == 0 && continue
        v2 = copy(vals); v2[(o.kid .== i) .| (o.kid .== j)] .*= 1.05
        W2 = plaquette_mats(o, v2); d = 0.0
        for side in (:bottom, :top)
            _, U = character_vectors(o, W2, side); d = max(d, maximum(abs, U' * U - I))
        end
        tried += 1; det += d > 1e-9
    end
    res["control_rescaled_tried"] = tried; res["control_rescaled_detected"] = det; res["Jc"] = Jc
    # control: the corner sign rule removed (expected NOT to be detected: the test is blind to signs)
    PHASE_RULE[] = false
    o2 = build_ops(L, J2)
    PHASE_RULE[] = true
    _, U = character_vectors(o2, plaquette_mats(o2, o2.ampF[o2.ks]), :bottom)
    res["control_no_sign_rule_gram_dev"] = maximum(abs, U' * U - I)
    @printf("L=%d cutoff %d/2 dim %d: %d vectors, Gram dev %.2e (bottom) %.2e (top), weight dev %.2e / %.2e over %d weights; controls: rescaled configuration (labels <= %d/2) detected %d of %d, no sign rule Gram dev %.2e\n",
        L, J2, length(o.basis), res["n_vectors"], res["gram_dev_bottom"], res["gram_dev_top"], res["weight_dev_bottom"], res["weight_dev_top"], res["n_weights"],
        Jc, det, tried, res["control_no_sign_rule_gram_dev"]); flush(stdout)
    res
end

function tojson(d)
    "{" * join(["\"$k\":" * (v isa AbstractString ? "\"$v\"" : string(v)) for (k, v) in sort(collect(d); by = first)], ",") * "}"
end

outp = ARGS[1]
all_res = String[]
for a in ARGS[2:end]
    L, J2, Jc, ns = parse.(Int, split(a, ":"))
    push!(all_res, tojson(run_case(L, J2, Jc, ns)))
    open(outp, "w") do f
        print(f, "[\n", join(all_res, ",\n"), "\n]\n")
    end
end
