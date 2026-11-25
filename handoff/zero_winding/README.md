# Zero-winding theorem (Theorem B): seeds, Lean certificates, second implementation

Sector c = +1 of the winding charge c = (-1)^(2 j_b + 2 j_t) of the SU(2) plaquette ladder, couplings 0 <= lambda <= 12.

## Pipeline
1. `make_tiling.py` -> `tiling.json`: 760 intervals (width 1/320 on [0,1], 1/160 on [1,2], 1/40 on [2,6], 1/20 on [6,12]) with the
   inverse temperature and cutoffs used on each (j* = 5/2, trial cutoff 2 up to lambda = 6; j* = 3, trial cutoff 5/2 beyond).
   None of these choices is trusted; they only affect how good the bounds are.
2. `even_seeds.jl` -> `even_seeds.jsonl`: rigorous upper bounds on the two seed defects of each interval (Julia, Float64
   intervals; the machinery of ../replay/ladder_replay.jl restricted to the sector; trial vector from the interval midpoint).
3. `gen_lean_even.py` (seeds padded by 3e-4; upstream's chain_certificate.jl) and `split_lean_even.py` -> the Lean files
   ../lean/GaugeGaps/LadderEven/{Defs,Part1..4}.lean, LadderEvenIntervals.lean; `LadderEvenIntervals_monolithic.lean.txt`
   is the unsplit list (it compiles but needs more memory than this machine has to build). `even_lean_bounds.json`: bounds.
4. `even_replay.py` (second implementation, Python): `compute` -> `even_replay_A.jsonl` (intervals 1-640), `even_replay_B.jsonl`
   (641-760); `check` compares against the seeds in the Lean files -> `even_replay_check.json`.
   Exact integer arithmetic (FLINT) for the similarity transform in the Tr exp bound, Arb balls for scalars, sympy 6j symbols,
   26-bit integer trial vectors. See the file header for what is and is not shared with the Julia code.

## Result
See `even_replay_check.json` and ../OVERNIGHT-LOG.md.
