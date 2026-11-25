# Independent replay of the ladder certificates, and two tests of the matrix elements

Everything here is Julia, written from the statements in the note (Lemmas 3 and 4, the cited corner formula),
not from the Python that produced the certificates. Run with any Julia environment that has
IntervalArithmetic (1.x) and KrylovKit; the CertifiedGaps checkout's `code/julia` project has both.

    julia --project=<env> ladder_replay.jl ../lean/GaugeGaps/LadderIntervals.lean ladder_replay_results.json
    julia --project=<env> commutator_test.jl commutator_test.json 2:7:5:1000000 3:6:4:1000000
    julia --project=<env> peter_weyl_test.jl peter_weyl_test.json 2:5:5:60 3:5:4:40 4:4:3:20

## Files
- `ladder_ops.jl`          spin-network basis and plaquette operators; 6j symbols by Racah's sum in exact rationals;
                           self-tests (W exactly symmetric, plaquettes commute, norm of tr U/2 at most 1)
- `ladder_replay.jl`       for each of the 240 intervals: reads the seeds s0, t0 from the Lean file and proves
                           1 - s0 <= spatial purity (n0 = 2) and 1 - t0 <= thermal purity (L = 4) on the whole interval,
                           for every flux cutoff >= the one used. These are the hypotheses `hs`, `ht` of `gap_on_interval`.
- `ladder_replay_results.json`, `replay.log`      final run: 240 of 240 pass, smallest margin 9.7e-5 of the defect (about 2 minutes)
- `ladder_replay_results_first_run.json`, `replay_first_run.log`, `LadderIntervals_first_version.lean.txt`
                           first run against the first version of the Lean file (seeds padded by 1e-6): 238 of 240.
                           Intervals 13 and 24 fail by 6e-6 and 5e-7 of the defect: two valid trial vectors give slopes w that
                           differ by up to 3e-8. Fix: seeds padded by 1e-4 (gen_lean_ladder_intervals.py), bounds unchanged to 4 decimals.
- `commutator_test.jl`     [tr U_p, tr U_q] = 0 on states one unit inside the cutoff. Sign-sensitive. Exhaustive controls:
                           `commutator_test.json`/`.log` (every local configuration within the certificates' label range),
                           `commutator_test_L2.json`, `commutator_test_L3_small.json` identify the two undetected flips
                           (the move out of the vacuum and its reverse; spectrum exactly unchanged).
- `peter_weyl_test.jl`     characters of independent loops are orthonormal; fixes the overall scale; blind to signs; partial coverage.

## What is and is not independent
Shared with the original: the mathematics (Lemma 3, Lemma 4, the corner formula) and the author.
Different: language, 6j evaluation, arithmetic (Float64 intervals vs Arb balls), the bound on Tr exp
(eigenvector basis + Gershgorin + Courant-Fischer vs ball matrix exponential), the label sums (exact integer
counts vs ball transfer matrix), the trial vectors, and the target (the Lean seeds, not the Python output).
Not trusted: LAPACK eigenvectors and Lanczos vectors (any vectors give valid bounds). Trusted: IntervalArithmetic.jl.

## Added for Theorem B (zero-winding sector)
- `ladder_replay.jl` has a `sector` option (default: all sectors) and a `lam_vec` option for the trial vector; the replay of
  Theorem A was rerun after these changes: 240 of 240.
- `commutator_test_B_L2.json/.log` (2 plaquettes at cutoff 9/2, every local configuration with labels up to 7/2) and
  `commutator_test_B_L3.json/.log` (3 plaquettes at cutoff 7/2, 3000 sampled configurations with labels up to 5/2).

## Added Tuesday 24 Nov

- `ising_map_test.jl`, `ising_map_test.json`: literature anchor at flux cutoff 1/2. In the sector c = +1 the operators of
  `ladder_ops.jl` have the same spectrum as the spin chain of X. Yao, arXiv:2303.14264 eq. (11) (Ising chain with longitudinal
  field and a transverse term carrying a factor 1 or -1/2 per neighbouring plaquette), to 2e-13 on rings of 2 to 8 plaquettes
  at lambda = 0.5, 2, 6, 12. Control (neighbour factor 0.45 instead of 1/2): differs by >= 0.016. Sees normalisation and the
  sizes 1, 1/2, 1/4 of the amplitudes; blind to signs; says nothing above label 1/2.

      julia --project=<env> ising_map_test.jl ising_map_test.json

- Regression after the changes made for Theorem C (`ground_lower`, the tail ratio computed without underflow):
  `ladder_replay_results_regression.json`, `ladder_replay_regression.log`: Theorem A replay 240/240, worst slack 9.74e-5
  (unchanged). Python side: intervals 1, 2, 639, 640, 760 of Theorem B recomputed with the modified `even_replay.py`: floats identical
  to the stored rows.

- `published_formula_test.jl`, `published_formula_test.json`, `published_formula_test_control.json`: the operator tables against a
  literal one-piece evaluation of the plaquette matrix element printed in the supplemental material of arXiv:2303.14264 (cited
  there to Klco, Stryker, Savage 2020 and ARahman, Lewis, Mendicelli, Powell 2021). Exact comparison of sign and rational square
  for every local configuration in the tables: 238,944 (2 plaquettes, cutoff 9/2), 1,386,328 (3 plaquettes, cutoff 7/2),
  133,900 (4 plaquettes, cutoff 5/2): no disagreement. Control with the corner sign rule off: see the control file.
  (The 3-plaquette run needs about 3 GB.) This shows the corner formula IS that published formula, not that the formula is right.

      julia --project=<env> published_formula_test.jl published_formula_test.json 2:9 3:7 4:5
