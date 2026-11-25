# ladder_ops.jl -- the SU(2) ladder in the spin-network basis, written from the cited plaquette matrix elements.
# Shared by ladder_replay.jl (the certificate replay) and peter_weyl_test.jl (a test that uses no 6j symbol).

using IntervalArithmetic, LinearAlgebra, SparseArrays

const IV = Interval{Float64}
ri(q::Rational) = interval(Float64(numerator(q))) / interval(Float64(denominator(q)))   # exact for small integers
ri(n::Integer) = interval(Float64(n))
up(x::IV) = sup(x)
lo(x::IV) = inf(x)

# ------------------------------------------------------------------ exact 6j symbols (doubled arguments)

tri(a, b, c) = iseven(a + b + c) && abs(a - b) <= c <= a + b
fct(n) = factorial(big(n))
delta2(a, b, c) = fct((a + b - c) ÷ 2) * fct((a - b + c) ÷ 2) * fct((b + c - a) ÷ 2) // fct((a + b + c) ÷ 2 + 1)

"""{a b c; d e f} = q * sqrt(r) with q, r exact rationals (Racah's single sum). Arguments are doubled spins."""
function sixj(a, b, c, d, e, f)
    (tri(a, b, c) && tri(a, e, f) && tri(d, b, f) && tri(d, e, c)) || return (big(0) // 1, big(0) // 1)
    r = delta2(a, b, c) * delta2(a, e, f) * delta2(d, b, f) * delta2(d, e, c)
    al = ((a + b + c) ÷ 2, (a + e + f) ÷ 2, (d + b + f) ÷ 2, (d + e + c) ÷ 2)
    be = ((a + b + d + e) ÷ 2, (b + c + e + f) ÷ 2, (c + a + f + d) ÷ 2)
    q = big(0) // 1
    for t in maximum(al):minimum(be)
        q += (isodd(t) ? -1 : 1) * fct(t + 1) // (prod(fct(t - x) for x in al) * prod(fct(y - t) for y in be))
    end
    (q, r)
end

const PHASE_RULE = Ref(true)      # set to false only by the negative control of peter_weyl_test.jl

"""Corner factor of the plaquette operator: external leg a, loop legs (in, out) -> (in', out').
F = (-1)^(a + j_out + 1/2 + j_in') sqrt((2 j_in + 1)(2 j_out' + 1)) {a j_out j_in; 1/2 j_in' j_out'}.
Returned as (sign, F^2) with F^2 an exact rational."""
function corner(a, jin, jout, jinn, joutn)
    q, r = sixj(a, jout, jin, 1, jinn, joutn)
    q == 0 && return (0, big(0) // 1)
    ph = (a + jout + 1 + jinn) ÷ 2
    (Int(sign(q)) * ((isodd(ph) && PHASE_RULE[]) ? -1 : 1), q^2 * r * (jin + 1) * (joutn + 1))
end

# ------------------------------------------------------------------ basis and operators

"""Admissible labelings of the periodic ladder with L plaquettes, doubled spins <= J2.
State layout: (b_1, t_1, r_1, ..., b_L, t_L, r_L); vertex (x, bottom) joins b_{x-1}, b_x, r_x, vertex (x, top) joins
t_{x-1}, t_x, r_x."""
function ladder_basis(L, J2)
    out = Vector{Vector{Int8}}()
    st = zeros(Int8, 3L)
    function rec(x)
        if x > L
            if tri(st[3L-2], st[1], st[3]) && tri(st[3L-1], st[2], st[3])
                push!(out, copy(st))
            end
            return
        end
        for b in 0:J2, t in 0:J2, r in 0:J2
            if x > 1 && !(tri(st[3x-5], b, r) && tri(st[3x-4], t, r))
                continue
            end
            st[3x-2] = b; st[3x-1] = t; st[3x] = r
            rec(x + 1)
        end
    end
    rec(1)
    out
end

struct Ops
    L::Int
    J2::Int
    basis::Vector{Vector{Int8}}
    diag4::Vector{Int}            # sum over links of j2 (j2 + 2) = 4 sum j(j+1)
    rows::Vector{Int32}
    cols::Vector{Int32}
    ks::Vector{Int32}             # amplitude class
    plaq::Vector{Int8}            # which plaquette produced the entry
    kid::Vector{Int32}            # local configuration (8 labels and the move) of the entry, index into `keys`
    keys::Vector{NTuple{12,Int}}  # (b, t, r, r', a_bottom_prev, a_top_prev, a_bottom_next, a_top_next, db, dt, dr, dr')
    amps::Vector{Tuple{Int,Rational{BigInt}}}   # (sign, square) of the entry of W = sum_p tr U_p / 2
    ampF::Vector{Float64}
    ampI::Vector{IV}
end

function amp_interval(s, sq)
    setprecision(BigFloat, 256) do
        v = sqrt(BigFloat(numerator(sq)) / BigFloat(denominator(sq)))
        a = prevfloat(Float64(v, RoundDown)); b = nextfloat(Float64(v, RoundUp))
        s > 0 ? interval(a, b) : interval(-b, -a)
    end
end

function build_ops(L, J2)
    basis = ladder_basis(L, J2)
    q = J2 + 1
    code(st) = foldl((acc, s) -> acc * q + s, st; init = 0)
    idx = Dict{Int,Int32}(code(st) => Int32(i) for (i, st) in enumerate(basis))
    diag4 = [sum(Int(j) * (Int(j) + 2) for j in st) for st in basis]
    amps = Tuple{Int,Rational{BigInt}}[]; ampid = Dict{Tuple{Int,Rational{BigInt}},Int32}()
    ctab = Dict{NTuple{5,Int},Tuple{Int,Rational{BigInt}}}()
    cor(a, i, o, i2, o2) = get!(() -> corner(a, i, o, i2, o2), ctab, (a, i, o, i2, o2))
    mtab = Dict{NTuple{12,Int},Int32}()
    keyid = Dict{NTuple{12,Int},Int32}(); keys = NTuple{12,Int}[]
    rows = Int32[]; cols = Int32[]; ks = Int32[]; plaq = Int8[]; kid = Int32[]
    new = zeros(Int8, 3L)
    for (i, st) in enumerate(basis), x in 1:L
        y = x == L ? 1 : x + 1; z = x == 1 ? L : x - 1
        b, t, r, rp = Int(st[3x-2]), Int(st[3x-1]), Int(st[3x]), Int(st[3y])
        abp, atp, abn, atn = Int(st[3z-2]), Int(st[3z-1]), Int(st[3y-2]), Int(st[3y-1])
        for db in (1, -1), dt in (1, -1), dr in (1, -1), drp in (1, -1)
            bn, tn, rn, rpn = b + db, t + dt, r + dr, rp + drp
            (min(bn, tn, rn, rpn) < 0 || max(bn, tn, rn, rpn) > J2) && continue
            key = (b, t, r, rp, abp, atp, abn, atn, db, dt, dr, drp)
            k = get!(mtab, key) do
                sg = 1; sq = big(1) // 1
                # corners: bottom-left, bottom-right, top-right, top-left; the loop runs r -> b -> r' -> t -> r
                for (a, jin, jout, jinn, joutn) in ((abp, r, b, rn, bn), (abn, b, rp, bn, rpn), (atn, rp, t, rpn, tn), (atp, t, r, tn, rn))
                    s, c2 = cor(a, jin, jout, jinn, joutn)
                    if s == 0
                        sg = 0; break
                    end
                    sg *= s; sq *= c2
                end
                sg == 0 ? Int32(0) : get!(ampid, (sg, sq / 4)) do
                    push!(amps, (sg, sq / 4)); Int32(length(amps))
                end
            end
            k == 0 && continue
            copyto!(new, st); new[3x-2] = bn; new[3x-1] = tn; new[3x] = rn; new[3y] = rpn
            j = get(idx, code(new), Int32(0))
            j == 0 && continue
            push!(rows, j); push!(cols, Int32(i)); push!(ks, k); push!(plaq, Int8(x))
            push!(kid, get!(keyid, key) do
                push!(keys, key); Int32(length(keys))
            end)
        end
    end
    Ops(L, J2, basis, diag4, rows, cols, ks, plaq, kid, keys, amps, [s * sqrt(Float64(sq)) for (s, sq) in amps], [amp_interval(s, sq) for (s, sq) in amps])
end

# ------------------------------------------------------------------ falsification tests of the operator

"""W must be exactly symmetric: entry (r, c) and entry (c, r) carry the same (sign, square). Returns the number of violations."""
function test_symmetric(o::Ops)
    d = Dict{Tuple{Int32,Int32,Int8},Int32}()
    for (r, c, k, p) in zip(o.rows, o.cols, o.ks, o.plaq)
        haskey(d, (r, c, p)) && error("duplicate entry")
        d[(r, c, p)] = k
    end
    bad = 0
    for ((r, c, p), k) in d
        k2 = get(d, (c, r, p), Int32(0))
        (k2 != 0 && o.amps[k2] == o.amps[k]) || (bad += 1)
    end
    bad
end

"""Plaquette operators on different plaquettes commute; with a cutoff this must hold on input states with every
label <= J2 - 2. Also ||tr U_p / 2|| <= 1. Returns (max commutator entry on those columns, max |eigenvalue| of W_1)."""
function test_commute_norm(o::Ops)
    n = length(o.basis)
    Wp = [sparse(o.rows[o.plaq.==p], o.cols[o.plaq.==p], o.ampF[o.ks[o.plaq.==p]], n, n) for p in 1:o.L]
    inner = findall(st -> maximum(st) <= o.J2 - 2, o.basis)
    worst = 0.0
    for p in 1:o.L, p2 in p+1:o.L
        C = Wp[p] * Wp[p2] - Wp[p2] * Wp[p]
        worst = max(worst, maximum(abs, C[:, inner]; init = 0.0))
    end
    nrm = n <= 6000 ? maximum(abs, eigvals(Symmetric(Matrix(Wp[1])))) : NaN
    (worst, nrm, length(inner))
end

