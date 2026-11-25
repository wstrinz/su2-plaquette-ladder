# commutator_test.jl -- a sign-sensitive test of the plaquette matrix elements that uses no 6j symbol in its target.
#
# Fact used: tr U_p and tr U_q are multiplication operators, so they commute. With a flux cutoff this holds exactly
# on input states whose labels are all <= cutoff - 1 (two applications raise a label by at most 1). The corner
# factors enter with their signs through the interference of the two orders.
# Controls: (A) the corner sign rule removed; (B) the sign of one local configuration (8 labels and a move, together
# with the reverse move) flipped, for a random sample of configurations whose labels are within `Jc`, the largest
# label the certificates use; (C) the same configurations rescaled by 1.05. A control is "detected" when the commutator on inner states exceeds 1e-9.
#
# usage: julia commutator_test.jl OUT.json L:J2:Jc:nsample [...]

using Printf, Random
include(joinpath(@__DIR__, "ladder_ops.jl"))

function mats(o, vals, idx)             # per-plaquette matrices from the entries listed in idx
    n = length(o.basis)
    [begin
        e = [i for i in idx if o.plaq[i] == p]
        sparse(o.rows[e], o.cols[e], vals[e], n, n)
    end for p in 1:o.L]
end

"""max over pairs p<q and inner columns of |A_p B_q - B_q A_p|; Ain, Bin are the matrices restricted to inner columns."""
function comm_max(L, A, Ain, B, Bin)
    worst = 0.0
    for p in 1:L, q in p+1:L
        C = A[p] * Bin[q] - B[q] * Ain[p]
        worst = max(worst, maximum(abs, nonzeros(C); init = 0.0))
    end
    worst
end

function run_case(L, J2, Jc, ns)
    o = build_ops(L, J2); n = length(o.basis)
    vals = o.ampF[o.ks]
    inner = findall(st -> maximum(st) <= J2 - 2, o.basis)
    W = mats(o, vals, eachindex(vals)); Win = [w[:, inner] for w in W]
    base = comm_max(L, W, Win, W, Win)
    PHASE_RULE[] = false; o2 = build_ops(L, J2); PHASE_RULE[] = true
    W2 = mats(o2, o2.ampF[o2.ks], eachindex(o2.ks)); W2in = [w[:, inner] for w in W2]
    nosign = comm_max(L, W2, W2in, W2, W2in)
    o2 = nothing; W2 = nothing; W2in = nothing
    # controls B and C
    keyidx = Dict(k => i for (i, k) in enumerate(o.keys))
    relevant = [i for (i, k) in enumerate(o.keys) if maximum(k[1:8]) <= Jc && max(k[1] + k[9], k[2] + k[10], k[3] + k[11], k[4] + k[12]) <= Jc]
    perm = sortperm(o.kid); first_of = fill(0, length(o.keys) + 1)
    for (pos, e) in enumerate(perm)
        first_of[o.kid[e]] == 0 && (first_of[o.kid[e]] = pos)
    end
    first_of[end] = length(perm) + 1
    for i in length(o.keys):-1:1
        first_of[i] == 0 && (first_of[i] = first_of[i+1])
    end
    entries_of(i) = perm[first_of[i]:first_of[i+1]-1]
    rng = MersenneTwister(11); det = 0; det2 = 0; tried = 0; mind = Inf; mind2 = Inf; missed = NTuple{12,Int}[]
    for i in shuffle(rng, relevant)[1:min(ns, length(relevant))]
        k = o.keys[i]
        rev = (k[1] + k[9], k[2] + k[10], k[3] + k[11], k[4] + k[12], k[5], k[6], k[7], k[8], -k[9], -k[10], -k[11], -k[12])
        j = get(keyidx, rev, 0); j == 0 && continue
        E = mats(o, vals, vcat(entries_of(i), entries_of(j))); Ein = [e[:, inner] for e in E]
        # W' = W + f E:  [W'_p, W'_q] = [W_p, W_q] + f ([E_p, W_q] + [W_p, E_q]) + f^2 [E_p, E_q];  f = -2 flips the sign, f = 0.05 rescales
        w1 = 0.0; w2 = 0.0
        for p in 1:L, q in p+1:L
            A = (E[p] * Win[q] - W[q] * Ein[p]) + (W[p] * Ein[q] - E[q] * Win[p]); B = E[p] * Ein[q] - E[q] * Ein[p]
            w1 = max(w1, maximum(abs, nonzeros(-2 .* A + 4 .* B); init = 0.0))
            w2 = max(w2, maximum(abs, nonzeros(0.05 .* A + 0.0025 .* B); init = 0.0))
        end
        tried += 1; det += w1 > 1e-9; det2 += w2 > 1e-9; mind = min(mind, w1); mind2 = min(mind2, w2)
        w1 > 1e-9 || push!(missed, k)
    end
    # a flip the commutator cannot see: is it a change of basis? compare spectra of H = H_E/3 - 1.7 W directly (small cases only)
    spec_dev = -1.0
    if !isempty(missed) && n <= 10000
        Hd(v) = Matrix(spdiagm(0 => o.diag4 ./ 3) - 1.7 .* sparse(o.rows, o.cols, v, n, n))
        e0 = eigvals(Symmetric(Hd(vals))); spec_dev = 0.0
        for k in missed
            rev = (k[1] + k[9], k[2] + k[10], k[3] + k[11], k[4] + k[12], k[5], k[6], k[7], k[8], -k[9], -k[10], -k[11], -k[12])
            v2 = copy(vals); for e in vcat(entries_of(keyidx[k]), entries_of(keyidx[rev])); v2[e] = -v2[e]; end
            spec_dev = max(spec_dev, maximum(abs, eigvals(Symmetric(Hd(v2))) - e0))
        end
    end
    println("   undetected sign flips: ", missed, isempty(missed) ? "" : "  spectrum change under those flips: $(spec_dev)")
    @printf("L=%d cutoff %d/2 (dim %d, %d inner states, %d local configurations, %d within %d/2): commutator %.2e; no sign rule %.2e; sign flip detected %d of %d (smallest effect %.2e), 5%% rescaling detected %d of %d (smallest effect %.2e)\n",
        L, J2, n, length(inner), length(o.keys), length(relevant), Jc, base, nosign, det, tried, mind, det2, tried, mind2); flush(stdout)
    @sprintf("{\"L\":%d,\"J2\":%d,\"Jc\":%d,\"dim\":%d,\"inner_states\":%d,\"local_configurations\":%d,\"within_Jc\":%d,\"commutator_max\":%.3e,\"control_no_sign_rule\":%.3e,\"control_flips_tried\":%d,\"control_flips_detected\":%d,\"control_flip_min_effect\":%.3e,\"control_rescale_detected\":%d,\"control_rescale_min_effect\":%.3e}",
        L, J2, Jc, n, length(inner), length(o.keys), length(relevant), base, nosign, tried, det, mind, det2, mind2)
end

outp = ARGS[1]; res = String[]
for a in ARGS[2:end]
    L, J2, Jc, ns = parse.(Int, split(a, ":"))
    push!(res, run_case(L, J2, Jc, ns))
    open(f -> print(f, "[\n", join(res, ",\n"), "\n]\n"), outp, "w")
end
