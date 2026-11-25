import GaugeGaps.LadderEvenIntervals
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Zero-winding sector: the certified rate exceeds 1 on every interval of `[0, 12]`

`log r / β₀ > 1` is checked in rational arithmetic: with `β₀ = p / q` in lowest terms it follows from
`2.7182818286 ^ p < r ^ q` and `exp 1 < 2.7182818286`. So on every interval the abstract theorem gives a gap
greater than `1` (in units where one unit of fundamental flux on a link costs `1`).
-/

open Real CertifiedGaps

namespace GaugeGaps.LadderEven

/-- Rational test implying `1 < log r / β₀`. -/
def gtOneB (I : Interval) : Bool :=
  decide (0 < I.β₀) && (decide (0 < I.cert.r) &&
    decide ((27182818286 / 10000000000 : ℚ) ^ I.β₀.num.toNat < I.cert.r ^ I.β₀.den))

theorem one_lt_of_gtOneB {I : Interval} (h : gtOneB I = true) : 1 < log (I.cert.r : ℝ) / (I.β₀ : ℝ) := by
  simp only [gtOneB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hβ, hr, hpow⟩ := h
  have hβr : (0 : ℝ) < (I.β₀ : ℝ) := by exact_mod_cast hβ
  have hr0 : (0 : ℝ) < (I.cert.r : ℝ) := by exact_mod_cast hr
  rw [lt_div_iff₀ hβr, one_mul, Real.lt_log_iff_exp_lt hr0]
  have hnum : 0 ≤ I.β₀.num := (Rat.num_pos.mpr hβ).le
  have hcast : ((I.β₀.num.toNat : ℕ) : ℝ) = (I.β₀.den : ℝ) * (I.β₀ : ℝ) := by
    have h1 : ((I.β₀.num.toNat : ℕ) : ℤ) = I.β₀.num := Int.toNat_of_nonneg hnum
    have h2 : (I.β₀ : ℝ) = (I.β₀.num : ℝ) / (I.β₀.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den I.β₀).symm
    have h3 : ((I.β₀.num.toNat : ℕ) : ℝ) = (I.β₀.num : ℝ) := by exact_mod_cast h1
    have hd : (I.β₀.den : ℝ) ≠ 0 := by exact_mod_cast I.β₀.den_nz
    rw [h3, h2]; field_simp
  have hE : exp (I.β₀ : ℝ) ^ I.β₀.den = exp 1 ^ I.β₀.num.toNat := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_one, hcast]
  have hn0 : I.β₀.num.toNat ≠ 0 := by
    have : 0 < I.β₀.num := Rat.num_pos.mpr hβ
    omega
  have hlt : exp (I.β₀ : ℝ) ^ I.β₀.den < (I.cert.r : ℝ) ^ I.β₀.den := by
    rw [hE]
    calc exp 1 ^ I.β₀.num.toNat < (2.7182818286 : ℝ) ^ I.β₀.num.toNat :=
          pow_lt_pow_left₀ Real.exp_one_lt_d9 (exp_pos 1).le hn0
      _ = (((27182818286 / 10000000000 : ℚ) ^ I.β₀.num.toNat : ℚ) : ℝ) := by push_cast; norm_num
      _ < (I.cert.r : ℝ) ^ I.β₀.den := by exact_mod_cast hpow
  exact lt_of_pow_lt_pow_left₀ _ hr0.le hlt

set_option maxRecDepth 1000000 in
theorem part1_gtOne : ∀ I ∈ part1, gtOneB I = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem part2_gtOne : ∀ I ∈ part2, gtOneB I = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem part3_gtOne : ∀ I ∈ part3, gtOneB I = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem part4_gtOne : ∀ I ∈ part4, gtOneB I = true := by decide +kernel

theorem intervals_gtOne : ∀ I ∈ intervals, 1 < log (I.cert.r : ℝ) / (I.β₀ : ℝ) := by
  intro I hI
  simp only [intervals, List.mem_append] at hI
  rcases hI with ((h | h) | h) | h
  · exact one_lt_of_gtOneB (part1_gtOne I h)
  · exact one_lt_of_gtOneB (part2_gtOne I h)
  · exact one_lt_of_gtOneB (part3_gtOne I h)
  · exact one_lt_of_gtOneB (part4_gtOne I h)

/-- On every interval of the tiling of `[0, 12]`: seeds in, a gap greater than `1` out. -/
theorem gap_gt_one_on_interval {ι : ℕ → Type*} [∀ L, Fintype (ι L)] [∀ L, Nonempty (ι L)]
    (E : (L : ℕ) → ι L → ℝ) (hZ : HasSpatialMomentBounds E 2) {I : Interval} (hI : I ∈ intervals)
    (hs : 1 - (I.cert.sAt 0 : ℝ) ≤ spatialPurity E 2 I.β₀)
    (ht : 1 - (I.cert.tAt 0 : ℝ) ≤ thermalPurity E (2 * 2) I.β₀) {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT (E L) 1 :=
  (gap_on_interval E hZ hI hs ht hL hLe).mono (intervals_gtOne I hI).le

end GaugeGaps.LadderEven
