# ladder_replay.jl -- independent replay of the 240 interval certificates of the SU(2) ladder theorem.
#
# Written from the statement of the note (Lemmas 3 and 4 and the cited plaquette matrix elements), not from the
# Python that produced the certificates. What is shared with the original: the mathematical specification, and
# nothing else. What differs:
#   language            Julia                                   (original: Python)
#   6j symbols          Racah's sum in exact rationals          (original: sympy.wigner_6j)
#   arithmetic          IntervalArithmetic.jl, Float64 intervals (original: Arb balls, 160 bits)
#   Tr exp              approximate eigenbasis + Weyl/Ostrowski  (original: Arb matrix exponential)
#   label sums          exact integer counts by direct enumeration (original: ball transfer matrix)
#   trial vectors       own Lanczos vectors, floating point       (original: 26-bit integer vectors)
#   target              the seeds s0, t0 written in LadderIntervals.lean, parsed from that file
#
# For each interval [la, lb] with seed temperature beta the replay proves, for every coupling in the interval and
# every flux cutoff >= the one used (hence in the limit),
#       1 - s0 <= exp(-beta E0(4) - 2 log Zup(2))   <= spatial purity at n0 = 2,
#       1 - t0 <= exp(-2 beta E0(4) - 4 log Zup(2)) <= thermal purity at L = 4,
# which are exactly the two hypotheses `hs`, `ht` of `gap_on_interval`. The second line uses Z(4) <= Z(2)^2, one of
# the moment inequalities that Lemmas 1 and 2 of the note supply; the replay does not re-prove that.
#
# usage: julia --project=<env with IntervalArithmetic, KrylovKit> ladder_replay.jl LadderIntervals.lean OUT.json [first last]

using KrylovKit, Printf, Random
include(joinpath(@__DIR__, "ladder_ops.jl"))

# ------------------------------------------------------------------ Lemma 3: upper bound on Z_2 for every cutoff >= jstar

struct ZUp
    js2::Int
    c::Rational{Int}
    nP::Int
    diagP::Vector{Int}
    Wpp::Matrix{IV}
    K::Matrix{IV}                 # P W Q' W P
    Nbig::Dict{Int,BigInt}        # labelings with all labels <= 16, by diag4
    Ntr::Dict{Int,BigInt}         # labelings with all labels <= js2, by diag4
end

insector(st, sector) = sector == :all || (sector == :even ? iseven(st[1] + st[2]) : isodd(st[1] + st[2]))     # Z2 winding charge (-1)^(2 j_b + 2 j_t), the same at every rung; sectors :all, :even, :odd

function label_counts(L, J2; sector = :all)
    cnt = Dict{Int,BigInt}()
    st = zeros(Int, 3L)
    function rec(x, d)
        if x > L
            if tri(st[3L-2], st[1], st[3]) && tri(st[3L-1], st[2], st[3]) && insector(st, sector)
                cnt[d] = get(cnt, d, big(0)) + 1
            end
            return
        end
        for b in 0:J2, t in 0:J2, r in 0:J2
            if x > 1 && !(tri(st[3x-5], b, r) && tri(st[3x-4], t, r))
                continue
            end
            st[3x-2] = b; st[3x-1] = t; st[3x] = r
            rec(x + 1, d + b * (b + 2) + t * (t + 2) + r * (r + 2))
        end
    end
    rec(1, 0)
    cnt
end

const JBIG2 = 16

function make_zup(js2, c; sector = :all)
    o = build_ops(2, js2 + 1)
    inS = [insector(st, sector) for st in o.basis]          # W preserves the sector, so everything below stays inside it
    inP = [inS[i] && maximum(st) <= js2 for (i, st) in enumerate(o.basis)]
    inQ = inS .& .!inP
    pidx = cumsum(inP); qidx = cumsum(inQ); nP = count(inP); nQ = count(inQ)
    Wpp = fill(interval(0.0), nP, nP); Wqp = fill(interval(0.0), nQ, nP)
    for (r, cc, k) in zip(o.rows, o.cols, o.ks)
        if inP[r] && inP[cc]
            Wpp[pidx[r], pidx[cc]] += o.ampI[k]
        elseif inP[cc]
            inQ[r] || error("plaquette operator left the sector")
            Wqp[qidx[r], pidx[cc]] += o.ampI[k]
        end
    end
    K = permutedims(Wqp) * Wqp
    Nbig = label_counts(2, JBIG2; sector = sector)
    Ntr = Dict{Int,BigInt}()
    for st in o.basis[inP]
        d = sum(Int(j) * (Int(j) + 2) for j in st); Ntr[d] = get(Ntr, d, big(0)) + 1
    end
    ZUp(js2, c, nP, o.diag4[inP], Wpp, K, Nbig, Ntr), o
end

fro(A) = sqrt(sum(x -> interval(mag(x))^2, A; init = interval(0.0)))

"""Upper bound on Tr exp(M) for a symmetric matrix enclosed entrywise by the interval matrix M.

Proof of the bound. Let V be the (floating-point, nearly orthogonal) eigenvector matrix, A = V^T M V, G = V^T V,
eta >= ||G - I||_2 with eta < 1 (so V is invertible), and u_i = A_ii + sum_{k != i} |A_ik|. Then diag(u) - A is
symmetric and diagonally dominant with non-negative diagonal, so x^T A x <= sum_i u_i x_i^2 for every x. With
y = V x we have y^T M y = x^T A x and y^T y = x^T G x in [(1 - eta), (1 + eta)] |x|^2. By Courant-Fischer applied to
the span of the coordinate vectors carrying the n - k + 1 smallest u, the k-th largest eigenvalue of M is at most
u_(k) / (1 - eta) if u_(k) >= 0 and u_(k) / (1 + eta) otherwise. Summing exponentials gives the bound; no ordering
is needed for the sum."""
function trace_exp_upper(M::Matrix{IV})
    n = size(M, 1)
    Mf = mid.(M); Mf = (Mf + Mf') / 2
    V = eigen(Symmetric(Mf)).vectors
    Vi = interval.(V)
    A = permutedims(Vi) * (M * Vi)                 # encloses V^T M V
    G = permutedims(Vi) * Vi
    for i in 1:n
        G[i, i] -= interval(1.0)
    end
    eta = interval(up(fro(G)))
    up(eta) < 0.25 || error("eigenvector matrix too far from orthogonal")
    tot = interval(0.0); plain = 0.0; worst = 0.0; umax = -Inf
    for i in 1:n
        R = interval(0.0)
        for k in 1:n
            k == i && continue
            R += interval(max(mag(A[i, k]), mag(A[k, i])))
        end
        u = interval(up(A[i, i] + R))
        ut = up(u) >= 0 ? u / (interval(1.0) - eta) : u / (interval(1.0) + eta)
        tot += exp(interval(up(ut)))
        umax = max(umax, up(ut))
        plain += exp(mid(A[i, i])); worst = max(worst, up(ut) - mid(A[i, i]))
    end
    interval(up(tot)), log(up(tot)) - log(plain), umax          # umax: upper bound on the largest eigenvalue of M
end

"""(upper bound on log Z_2(beta, lam) valid for every cutoff >= js2/2, tail / main, delta)."""
function log_zup(Z::ZUp, beta::Rational, lam::Rational)
    b = ri(beta); l = ri(lam); c = ri(Z.c); L = 2
    M = (b * l) .* Z.Wpp .+ (b * l * l / c) .* Z.K
    for i in 1:Z.nP
        M[i, i] += -(b / interval(3.0)) * ri(Z.diagP[i])       # e = 1: -beta (e/3) diag4
    end
    main, delta, _ = trace_exp_upper(M)
    # tail: exp(beta (lam L + c)) [S_all - S_{<= jstar}], S = sum over labelings of exp(-beta diag4 / 3)
    diff = interval(0.0)
    for (d, nb) in Z.Nbig
        m = nb - get(Z.Ntr, d, big(0))
        m < 0 && error("count mismatch")
        m == 0 && continue
        diff += interval(Float64(m, RoundDown), Float64(m, RoundUp)) * exp(-(b / interval(3.0)) * ri(d))
    end
    all(haskey(Z.Nbig, d) for d in keys(Z.Ntr)) || error("count mismatch")
    w(j2) = exp(-(b / interval(3.0)) * ri(j2 * (j2 + 2)))
    w1 = w(JBIG2 + 1)
    q = exp(-(b / interval(3.0)) * ri(2 * JBIG2 + 5))           # w(J+2)/w(J+1), written directly so that underflow of w cannot produce 0/0
    tau = w1 / (interval(1.0) - q)                  # sum over j2 > 16 of w(j2): the ratios decrease
    S1 = sum(w(j2) for j2 in 0:JBIG2) + tau
    rem = ri(3L) * tau * pown(S1, 3L - 1)
    tail = exp(b * (l * ri(L) + c)) * (diff + rem)
    z = main + tail
    (isguaranteed(z) && up(z) > 0) || error("unguaranteed interval")
    interval(up(log(interval(up(z))))), up(tail) / lo(main), delta
end

"""Lower bound on the lowest eigenvalue of H on 2 plaquettes (in the sector of Z), valid for every cutoff >= js2/2.
From the proof of Lemma 3: H >= A (+) B with A = PHP - (lam^2/c) P W Q' W P on ran P and B = H0 - (lam L + c) on ran Q.
So E0 >= min(lambda_min(A), min over labelings with some link above jstar of the electric energy - (lam L + c))."""
function ground_lower(Z::ZUp, lam::Rational)
    l = ri(lam); c = ri(Z.c); L = 2
    M = l .* Z.Wpp .+ (l * l / c) .* Z.K                       # M = -A  (beta = 1)
    for i in 1:Z.nP
        M[i, i] += -ri(Z.diagP[i]) / interval(3.0)
    end
    _, _, umax = trace_exp_upper(M)
    dmin = minimum(d for (d, nb) in Z.Nbig if nb - get(Z.Ntr, d, big(0)) > 0)      # labelings with largest label in (jstar, 8]
    dmin <= (JBIG2 + 1) * (JBIG2 + 3) || error("a labeling above the enumeration range could be lower")   # one link above 8 already costs more
    bmin = ri(dmin) / interval(3.0) - (l * ri(L) + c)
    min(-umax, lo(bmin))
end

# ------------------------------------------------------------------ Lemma 4: trial energy and slope at L = 4

struct Trial
    o::Ops
    Wf::SparseMatrixCSC{Float64,Int}
    v0::Base.RefValue{Vector{Float64}}
end

function make_trial(Jt2; L = 4)
    o = build_ops(L, Jt2)
    n = length(o.basis)
    Wf = sparse(o.rows, o.cols, o.ampF[o.ks], n, n)
    v = zeros(n); v[argmin(o.diag4)] = 1.0
    v .+= 1e-3 .* randn(MersenneTwister(1), n)
    Trial(o, Wf, Ref(v))
end

"""(upper bound on E0(4) at lam, lower bound on <W>, float eigenvalue) from a floating-point trial vector whose
Rayleigh quotient is evaluated in interval arithmetic. The vector is the Lanczos vector at the coupling `lam_vec`
(default lam); any vector gives a valid tangent line theta - (lam' - lam) w, and taking it at the midpoint of an
interval quarters the loss at the endpoints."""
function theta_w(T::Trial, lam::Rational; sector = :all, lam_vec::Rational = lam)
    o = T.o; n = length(o.basis)
    H = spdiagm(0 => o.diag4 ./ 3) - Float64(lam_vec) .* T.Wf
    H = (H + H') / 2
    vals, vecs, info = eigsolve(H, T.v0[], 1, :SR; ishermitian = true, tol = 1e-12, krylovdim = 40, maxiter = 400)
    info.converged >= 1 || @warn "Lanczos not converged" lam info.normres
    v = real.(vecs[1]); v ./= maximum(abs, v); T.v0[] = copy(v)
    if sector != :all                      # project the trial vector into the sector (exactly: set the other components to zero)
        for i in 1:n
            insector(o.basis[i], sector) || (v[i] = 0.0)
        end
    end
    den = interval(0.0); dsum = interval(0.0)
    for i in 1:n
        x = interval(v[i])^2
        den += x; dsum += ri(o.diag4[i]) * x
    end
    nk = length(o.amps)
    S = fill(interval(0.0), nk)
    @inbounds for e in eachindex(o.rows)
        S[o.ks[e]] += interval(v[o.rows[e]]) * interval(v[o.cols[e]])
    end
    wsum = interval(0.0)
    for k in 1:nk
        wsum += o.ampI[k] * S[k]
    end
    wexp = wsum / den
    theta = dsum / (interval(3.0) * den) - ri(lam) * wexp
    (isguaranteed(theta) && isguaranteed(wexp)) || error("unguaranteed interval")
    interval(up(theta)), interval(lo(wexp)), vals[1]
end

# ------------------------------------------------------------------ the Lean file

function parse_dec(s)
    m = match(r"^(\d+)(?:\.(\d+))?(?:e(-?\d+))?$", strip(s))
    m === nothing && error("cannot parse literal $s")
    frac = m.captures[2] === nothing ? "" : m.captures[2]
    ex = (m.captures[3] === nothing ? 0 : parse(Int, m.captures[3])) - length(frac)
    num = parse(BigInt, m.captures[1] * frac)
    ex >= 0 ? num * big(10)^ex // 1 : num // big(10)^(-ex)
end

function parse_rat(s)
    p = split(strip(s), "/")
    length(p) == 1 ? parse(Int, p[1]) // 1 : parse(Int, strip(p[1])) // parse(Int, strip(p[2]))
end

function read_lean(path)
    out = []
    for line in eachline(path)
        m = match(r"^\s*⟨([^,]+),([^,]+),([^,]+),\s*\{\s*s := \[([^\]]*)\],\s*t := \[([^\]]*)\],\s*r := ([^,]+),", line)
        m === nothing && continue
        push!(out, (la = parse_rat(m.captures[1]), lb = parse_rat(m.captures[2]), beta = parse_rat(m.captures[3]),
            s0 = parse_dec(split(m.captures[4], ",")[1]), t0 = parse_dec(split(m.captures[5], ",")[1]), r = parse_dec(m.captures[6])))
    end
    out
end

bigiv(q::Rational{BigInt}) = interval(Float64(q, RoundDown), Float64(q, RoundUp))

# ------------------------------------------------------------------ main

function main()
    lean, outp = ARGS[1], ARGS[2]
    ivs = read_lean(lean)
    first_i = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 1
    last_i = length(ARGS) >= 4 ? parse(Int, ARGS[4]) : length(ivs)
    println("intervals in Lean file: ", length(ivs)); flush(stdout)
    length(ivs) == 240 || error("expected 240 intervals")
    ivs[1].la == 0 && ivs[end].lb == 6 && all(ivs[i].lb == ivs[i+1].la for i in 1:239) || error("intervals do not tile [0, 6]")
    config(iv) = iv.lb <= 2 ? (3, 3, 10 // 1) : (4, 4, 12 // 1)      # (2 jstar, 2 J_trial, c)
    zcache = Dict{Any,Any}(); tcache = Dict{Int,Trial}(); lcache = Dict{Any,Any}()
    recs = String[]
    npass = 0; worst_s = Inf; worst_t = Inf
    t00 = time()
    for i in first_i:last_i
        iv = ivs[i]; js2, jt2, c = config(iv); t0 = time()
        Z = get!(zcache, (js2, c)) do
            z, o = make_zup(js2, c)
            bad = test_symmetric(o); comm, nrm, ninner = test_commute_norm(o)
            @printf("L=2 cutoff %d/2: dim %d, P-dim %d, W asymmetric entries %d, commutator %.2e on %d inner states, ||W_1|| = %.12f\n",
                js2 + 1, length(o.basis), z.nP, bad, comm, ninner, nrm); flush(stdout)
            (bad == 0 && comm < 1e-10 && nrm <= 1 + 1e-10) || error("operator self-test failed")
            z
        end
        T = get!(tcache, jt2) do
            t = make_trial(jt2)
            bad = test_symmetric(t.o)
            @printf("L=4 cutoff %d/2: dim %d, entries %d, amplitude classes %d, W asymmetric entries %d\n",
                jt2, length(t.o.basis), length(t.o.rows), length(t.o.amps), bad); flush(stdout)
            bad == 0 || error("operator self-test failed")
            t
        end
        la_ = get!(() -> log_zup(Z, iv.beta, iv.la), lcache, (js2, c, iv.beta, iv.la))
        lb_ = get!(() -> log_zup(Z, iv.beta, iv.lb), lcache, (js2, c, iv.beta, iv.lb))
        th, w, e0 = theta_w(T, iv.la)
        b = ri(iv.beta); d = ri(iv.lb - iv.la)
        x0s = -(b * th) - interval(2.0) * la_[1]; x1s = -(b * (th - d * w)) - interval(2.0) * lb_[1]
        x0t = -(interval(2.0) * b * th) - interval(4.0) * la_[1]; x1t = -(interval(2.0) * b * (th - d * w)) - interval(4.0) * lb_[1]
        ps = min(lo(exp(x0s)), lo(exp(x1s))); pt = min(lo(exp(x0t)), lo(exp(x1t)))        # purity lower bounds on the interval
        needs = up(interval(1.0) - bigiv(iv.s0)); needt = up(interval(1.0) - bigiv(iv.t0))
        ok = needs <= ps && needt <= pt
        npass += ok
        ms = (ps - needs) / (1 - ps); mt = (pt - needt) / (1 - pt)       # slack relative to the defect
        worst_s = min(worst_s, ms); worst_t = min(worst_t, mt)
        push!(recs, @sprintf("{\"i\":%d,\"la\":\"%s\",\"lb\":\"%s\",\"beta\":\"%s\",\"s0\":%.10g,\"t0\":%.10g,\"eps_s_replay\":%.12g,\"eps_t_replay\":%.12g,\"theta\":%.15g,\"w\":%.15g,\"logZup_a\":%.15g,\"logZup_b\":%.15g,\"tail_rel_b\":%.3g,\"eig_delta_b\":%.3g,\"rel_slack_s\":%.4g,\"rel_slack_t\":%.4g,\"pass\":%s}",
            i, string(iv.la), string(iv.lb), string(iv.beta), Float64(iv.s0), Float64(iv.t0), 1 - ps, 1 - pt, up(th), lo(w), up(la_[1]), up(lb_[1]), lb_[2], lb_[3], ms, mt, ok ? "true" : "false"))
        @printf("%3d [%s, %s] beta %s  eps_s %.6g <= %.6g  eps_t %.6g <= %.6g  %s  (%.1fs)\n", i, string(iv.la), string(iv.lb), string(iv.beta),
            1 - ps, Float64(iv.s0), 1 - pt, Float64(iv.t0), ok ? "ok" : "FAIL", time() - t0); flush(stdout)
        open(outp, "w") do f
            print(f, "{\"n_checked\":", length(recs), ",\"n_pass\":", npass, ",\"worst_rel_slack_s\":", worst_s, ",\"worst_rel_slack_t\":", worst_t, ",\"rows\":[\n", join(recs, ",\n"), "\n]}\n")
        end
    end
    @printf("checked %d, passed %d, worst relative slack: spatial %.3g, thermal %.3g, %.0fs\n", length(recs), npass, worst_s, worst_t, time() - t00)
end

if abspath(PROGRAM_FILE) == (@__FILE__)
    main()
end
