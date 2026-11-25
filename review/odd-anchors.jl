# Cross-check the new odd-sector anchors with the Julia interval implementation.
include(joinpath(@__DIR__, "..", "handoff", "replay", "ladder_replay.jl"))

function anchor_run(output, args)
    penalty = 12
    if length(args) >= 2 && args[1] == "--penalty"
        penalty = parse_rat(args[2])
        args = args[3:end]
    end
    penalty > 0 || error("the block penalty must be positive")
    isempty(args) && error("at least one coupling is required")
    model, _ = make_zup(6, penalty // 1; sector = :odd)
    open(output, "w") do io
        for arg in args
            x = parse(Int, arg)
            lower = Rational{BigInt}(ground_lower(model, x // 1))
            label = denominator(penalty) == 1 ? string(numerator(penalty)) : string('"', numerator(penalty), "/", denominator(penalty), '"')
            println(io, "{\"x\":\"", x, "\",\"two_j_star\":6,\"penalty\":", label, ",\"omega_lower\":\"",
                    numerator(lower), "/", denominator(lower), "\"}")
            flush(io)
        end
    end
end

anchor_run(ARGS[1], ARGS[2:end])
