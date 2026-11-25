import GaugeGaps.Z3Seed.Data

/-!
# The residual checks are not vacuous

The kernel checks of `Seed.lean` fail when the trial energy is moved by `5 · 10⁻⁵` (fifty times the
certified radius) or when the hopping is changed from `16` to `15`.
-/

namespace GaugeGaps.Z3Seed

theorem res2_shifted_fails : ¬ (residualSq 1 16 scale 2 v2 (lam2 + 10 ^ 6) *
    ((10 ^ 6 : ℕ) : ℤ) ^ 2 ≤ 4 * scale ^ 2 * dot 2 v2) := by decide +kernel

theorem res4_shifted_fails : ¬ (residualSq 1 16 scale 4 v4 (lam4 + 10 ^ 6) *
    ((10 ^ 6 : ℕ) : ℤ) ^ 2 ≤ 4 * scale ^ 2 * dot 4 v4) := by decide +kernel

theorem res4_other_coupling_fails : ¬ (residualSq 1 15 scale 4 v4 lam4 *
    ((10 ^ 6 : ℕ) : ℤ) ^ 2 ≤ 4 * scale ^ 2 * dot 4 v4) := by decide +kernel

end GaugeGaps.Z3Seed
