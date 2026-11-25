# GaugeGaps: Lean files

Built against a checkout of LionSR/CertifiedGaps (commit 77b5588, 18 Nov 2026) placed next to this folder
(see `lakefile.toml`), Lean 4.36.0-rc1 and the Mathlib revision that library pins. Nothing here has been sent upstream.

## Layout
- `GaugeGaps/RatMat.lean`                 integer matrices cast to the reals
- `GaugeGaps/{Z3,S3}GaugeHiggs.lean`      finite-group gauge-Higgs chains as `RPRing` instances; gap theorems with seeds as a hypothesis
- `GaugeGaps/SU2HalfGaugeHiggs.lean`      SU(2) gauge-Higgs chain at flux cutoff 1/2 (exact rational real basis, d = 5); same
- `GaugeGaps/Z2Ladder.lean`               Z2 split-link plaquette ladder cell (d = 8); same
- `GaugeGaps/PenaltyLimit.lean`           penalty limit: the constrained spectrum inherits the moment inequalities
- `GaugeGaps/Interval.lean`               the coupling-interval inequality
- `GaugeGaps/LadderIntervals.lean`        the 240 coupling intervals of the SU(2) ladder theorem: kernel-checked chain certificates,
                                         the tiling of [0, 6], and `gap_on_interval` (upstream's abstract theorem per interval; the two
                                         seed inequalities remain hypotheses and are replayed by ../replay/ladder_replay.jl)
- `GaugeGaps/LadderEven/{Defs,Part1..Part4}.lean`, `GaugeGaps/LadderEvenIntervals.lean`
                                         zero-winding sector (c = +1): 760 kernel-checked chain certificates on a tiling of [0, 12],
                                         split over four files to fit in memory; `tilesB`/`exists_interval` (every coupling in [0, 12]
                                         lies in an interval) and `gap_on_interval`; seeds replayed by ../zero_winding/even_replay.py
- `GaugeGaps/LadderEvenGtOne.lean`        `gap_gt_one_on_interval`: on every one of those intervals the certified rate exceeds 1
                                         (rational check of 2.7182818286^p < r^q with beta = p/q)
- `GaugeGaps/Lemma1Algebra.lean`          the algebraic core of Lemma 1 (split-link positivity), for an arbitrary group: the reflection rho
                                         is an involution commuting with the vertex gauge transformations; R (right translation in b'') R =
                                         left translation in b' by the same element; P o rho = Q; the rejoined plaquette holonomy is conjugate
                                         to Q P^-1; and for SU(2), tr(Q P^-1) = 2 sum q_k p_k with all four signs plus
- `GaugeGaps/StringTension.lean`          Lemma 6 in full (`string_tension`): from the moment inequalities in two sectors and four bounds on
                                         the ring of length 2, every level of the second sector on an even ring of length L lies at least
                                         sigma L above the lowest level of the first; and `gapGT_sum` (sector gap + that bound => gap for both)
- `GaugeGaps/TensionIntervals.lean`       Theorem C: 180 intervals tiling [0, 12], each with rational bounds on the four inputs of Lemma 6 at
                                         its endpoints and a certified sigma; kernel-checked `intervals_ok`, `intervals_tile`;
                                         `exists_interval`; `tension_on_interval` (string_tension at any point of an interval)
- `GaugeGaps/FullSpectrum.lean`           `full_gap_gt_one`: hypotheses of Theorems B and C => the union of the two sector spectra has a
                                         nondegenerate lowest level and gap > 1 at every even L >= 2 (`tension_gt_half`: every sigma > 1/2)
- `GaugeGaps/Z3Seed/`                     first hypothesis-free theorem (Z3 chain, e = 1, kappa = 16), model-specific proof
- `GaugeGaps/KernelSeed/`                 the generic construction:
    - `Gershgorin.lean`   form of a ring Hamiltonian >= its local Gershgorin function (any `RPRing`)
    - `Checker.lean`, `TailChecker.lean`   integer checker (`IntRing`: tables den*o, den*bond; packed vectors)
    - `Bridge.lean`       checker <-> `RPRing.hamiltonian`; residual => eigenvalue; classical count => eigenvalue count
    - `Seed.lean`         seeds from a located ground energy and the crude count
    - `Tail.lean`         sharper bound: counting domination at every threshold + dyadic classical tail
    - `SU2Half.lean`, `S3.lean`   integer tables of two models and the proofs that they represent the Lean models
    - `<Model>E<e>K<kappa>.lean`       generated point files (crude bound), `...Fine.lean` (sharper bound)
    - `Results.lean`      the final statements, numbers written out, with `#print axioms`

## Building
`lake build GaugeGaps` works on a large machine. On a 7 GB machine build the point files one at a time
(`lake build GaugeGaps.KernelSeed.SU2HalfE2K1`, ...): each needs about 4 GB, most of it Mathlib.
The 4-link kernel checks are split into chunks (one declaration each) to bound kernel memory.

## Regenerating
`gen_kernel_seed.py <model> <e> <kappa> <out.lean>` and `gen_kernel_tail.py ...` (models: su2half, s3) write the point files.
They need numpy, python-flint, and Julia 1.12.4 with the CertifiedGaps checkout for `chain_certificate.jl`.
The trial vectors come from floating-point diagonalisation and carry no trust: the kernel evaluates their residuals.
