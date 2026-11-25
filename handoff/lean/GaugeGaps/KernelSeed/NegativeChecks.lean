import GaugeGaps.KernelSeed.SU2HalfE2K1

/-!
# The generic kernel checks are not vacuous

For the `SU(2)` cutoff-`1/2` chain at `e = 2`, `κ = 1` on 2 links: the residual check fails when the
trial energy is moved by `1.7 · 10⁻⁵` (seventeen times the certified radius), and the classical count
is no longer `1` when the cut is raised by one unit.
-/

open GaugeGaps.KernelSeed

namespace GaugeGaps.SU2HalfSeed.E2K1

theorem res2_shifted_fails : ¬ (T.residualSq scale 2 v2 (lam2 + 10 ^ 6) * ((10 ^ 6 : ℕ) : ℤ) ^ 2 ≤
    T.den ^ 2 * scale ^ 2 * dot 5 2 v2) := by decide +kernel

theorem count2_raised_cut_fails : T.classicalCount 2 (cut2 + 1) ≠ 1 := by decide +kernel

end GaugeGaps.SU2HalfSeed.E2K1
