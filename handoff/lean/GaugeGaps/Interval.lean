import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Seeds on a whole coupling interval

Let `x` be a coupling, `Zn x` and `Z2n x` two partition functions (for instance on rings of `n` and `2n`
sites). Suppose that on `[a, b]`

* `log (Zn x)` is convex (true for `log Tr exp(A + x B)`),
* `Z2n x ≥ exp(-β (θ - (x - a) w))` (the variational bound from a trial state chosen at `a`, whose energy
  is `θ - (x - a) w`, linear in `x`),

and that `log (Zn a) ≤ ℓa`, `log (Zn b) ≤ ℓb`. Then for every `x ∈ [a, b]` the ratio `Z2n x / Zn x ^ k`
is at least the smaller of two endpoint expressions. With `k = 2` this bounds the spatial purity and with
`k = 4` (and `2β` in place of `β`) the thermal purity, so two endpoint computations give the seeds of the
purity criterion on the whole interval.
-/

open Real

namespace GaugeGaps

/-- An affine function on `[0, 1]` is at least the smaller of its endpoint values. -/
theorem min_le_affine {g₀ g₁ t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    min g₀ g₁ ≤ (1 - t) * g₀ + t * g₁ := by
  rcases le_total g₀ g₁ with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-- **Seeds on an interval.** See the module docstring. -/
theorem ratio_ge_on_interval {Zn Z2n : ℝ → ℝ} {a b β θ w ℓa ℓb : ℝ} (k : ℕ) (hab : a < b)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < Zn x)
    (hconv : ConvexOn ℝ (Set.Icc a b) fun x ↦ log (Zn x))
    (hlow : ∀ x ∈ Set.Icc a b, exp (-(β * (θ - (x - a) * w))) ≤ Z2n x)
    (ha : log (Zn a) ≤ ℓa) (hb : log (Zn b) ≤ ℓb) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    min (exp (-(β * θ) - k * ℓa)) (exp (-(β * (θ - (b - a) * w)) - k * ℓb)) ≤ Z2n x / Zn x ^ k := by
  have hba : 0 < b - a := sub_pos.2 hab
  set t := (x - a) / (b - a) with ht
  have ht₀ : 0 ≤ t := div_nonneg (sub_nonneg.2 hx.1) hba.le
  have ht₁ : t ≤ 1 := (div_le_one hba).2 (by linarith [hx.2])
  have hxa : x - a = t * (b - a) := by rw [ht]; field_simp
  have hxt : (1 - t) * a + t * b = x := by linarith [hxa]
  have hZ : 0 < Zn x := hpos x hx
  -- convexity of `log Zn` along the chord
  have hc : log (Zn x) ≤ (1 - t) * log (Zn a) + t * log (Zn b) := by
    have h := hconv.2 (Set.left_mem_Icc.2 hab.le) (Set.right_mem_Icc.2 hab.le) (sub_nonneg.2 ht₁) ht₀
      (by ring : 1 - t + t = 1)
    simpa [smul_eq_mul, hxt] using h
  have hlog : log (Zn x) ≤ (1 - t) * ℓa + t * ℓb := by
    have h₁ := mul_le_mul_of_nonneg_left ha (sub_nonneg.2 ht₁)
    have h₂ := mul_le_mul_of_nonneg_left hb ht₀
    linarith
  have hden : Zn x ^ k ≤ exp (k * ((1 - t) * ℓa + t * ℓb)) := by
    have h : Zn x ^ k = exp (k * log (Zn x)) := by rw [exp_nat_mul, exp_log hZ]
    rw [h]
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k))
  have key : exp ((1 - t) * (-(β * θ) - k * ℓa) + t * (-(β * (θ - (b - a) * w)) - k * ℓb)) ≤
      Z2n x / Zn x ^ k := by
    rw [le_div_iff₀ (pow_pos hZ k)]
    calc exp ((1 - t) * (-(β * θ) - k * ℓa) + t * (-(β * (θ - (b - a) * w)) - k * ℓb)) * Zn x ^ k
        ≤ exp ((1 - t) * (-(β * θ) - k * ℓa) + t * (-(β * (θ - (b - a) * w)) - k * ℓb)) *
            exp (k * ((1 - t) * ℓa + t * ℓb)) := mul_le_mul_of_nonneg_left hden (exp_pos _).le
      _ = exp (-(β * (θ - (x - a) * w))) := by
          rw [← exp_add, hxa]; congr 1; ring
      _ ≤ Z2n x := hlow x hx
  refine le_trans ?_ key
  have hmin := min_le_affine (g₀ := -(β * θ) - k * ℓa) (g₁ := -(β * (θ - (b - a) * w)) - k * ℓb) ht₀ ht₁
  rw [← exp_monotone.map_min]
  exact exp_le_exp.2 hmin

end GaugeGaps
