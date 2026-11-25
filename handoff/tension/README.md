# String tension (Theorem C) and the gap of the whole spectrum (Corollary)

For every coupling 0 <= lambda <= 12 and every even L >= 2:  E-(L) - E+(L) >= sigma(lambda) L, with E+/E- the lowest
eigenvalue of the SU(2) ladder Hamiltonian in the sector c = +1 / c = -1 of the winding charge.

- `tension_float.py`, `tension_float.json`       exploration with exact floating inputs (not a certificate)
- `lemma6_test.py`, `lemma6_test.json`           falsification test of Lemma 6 at one cutoff on 2, 4, 6 plaquettes: 72 cases, no
                                                 violation; control with the correction D dropped violated in 57
- `make_tiling.py`, `tiling.json`                180 intervals (width 1/20 up to 6, 1/10 beyond), temperatures and cutoffs (untrusted choices)
- `tension_seeds.jl`, `tension_seeds.jsonl`      Julia, Float64 intervals: sigma on every interval (uses ../replay/ladder_replay.jl)
- `gen_lean_tension.py`, `tension_certificate.json`   the certificate: per interval, rational bounds on the inputs of Lemma 6 at both
                                                 endpoints (Julia's values moved 2e-6 in the safe direction; eps by 3 parts in 1e4) and
                                                 sigma = the rational bound of Lemma 6, rounded down to 4 decimals. Writes the Lean file too.
- `make_corollary.py`, `corollary_full_gap.json` min(g+, L sigma): gap of the whole gauge-invariant spectrum, by coupling range
- `tension_replay.py`, `tension_replay_A/B/C.jsonl`, `tension_replay_check.json`
                                                 second implementation (Python: exact integers, Arb, sympy 6j). `check-lean` verifies, for
                                                 every certificate entry, the eight endpoint bounds and the defect bound (the hypotheses of
                                                 the Lean theorem) and, redundantly with the kernel, the rational arithmetic.
- `tension_seeds_check.json`                     the same check applied to the Julia rows
- `old/`                                         first certificate format (sigma only) and the partial replay against it
- Lean: ../lean/GaugeGaps/StringTension.lean      Lemma 6 itself (`string_tension`) and `gapGT_sum`
        ../lean/GaugeGaps/TensionIntervals.lean   the 180 certificate entries; kernel-checked: sigma <= bound of Lemma 6 at both endpoints
                                                 (with -log(1-x) <= x + x^2/2 + x^3/3 + x^4/4 + x^5/(1-x), proved there), tiling of [0, 12];
                                                 `tension_on_interval`: the conclusion at every point of an interval from the four inputs
                                                 interpolated linearly
        ../lean/GaugeGaps/FullSpectrum.lean       `full_gap_gt_one`: Theorem B's and Theorem C's hypotheses => gap > 1 for both sectors together

Why linear interpolation of the inputs is legitimate (paper, Lemma 6 section of the note): E-(2) is concave in lambda (lowest
eigenvalue of H0 - lambda W), log Z+ is convex (Lemma 4 b), the trial energy is affine (Lemma 4 a), eps is one bound for the interval.

Inputs of Lemma 6 on an interval: omega <= E-(2) (operator inequality behind Lemma 3, odd sector); l1 >= log Z+(2, beta1) (Lemma 3);
theta >= E+(2) (trial vector on 2 plaquettes); eps >= spatial seed defect of the even sector at beta (as in Theorem B).
