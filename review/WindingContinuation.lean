import GaugeGaps.FullSpectrum
import GaugeGaps.Lemma1Algebra
import GaugeGaps.LadderIntervals
import Mathlib.Analysis.Convex.Slope

/-!
Additional checks for the winding-energy continuation. The endpoint checks use the
actual handoff list. The real-variable theorem assumes that the sector energies
satisfy the corresponding variational and moment bounds, as in the manuscript.
-/
namespace GaugeGaps.WindingContinuation

open Tension

def densityUpper (I : TInterval) : ℚ :=
  (I.ℓb / 2 + I.β * I.θb / 2 +
    (logBar I.ε + logBar (sqDef I.ε)) / 4) / (I.β - I.β₁)

set_option maxRecDepth 1000000 in
theorem anchorRows :
    (intervals.any fun I => decide (I.lb = 113/10 ∧ 0 < I.β₁ ∧
      -(29333221/6000000 : ℚ) ≤ -I.ℓb / (2 * I.β₁))) = true ∧
    (intervals.any fun I => decide (I.lb = 12 ∧ densityUpper I ≤ -5.33611 ∧
      0.5584 ≤ I.σ)) = true := by decide +kernel

theorem evenSupport (evenDensity : ℝ → ℝ)
    (hc : ConcaveOn ℝ (Set.Ici 0) evenDensity)
    (hleft : -(29333221/6000000 : ℝ) ≤ evenDensity 11.3)
    (hright : evenDensity 12 ≤ -5.33611)
    {h : ℝ} (hh : 0 ≤ h) :
    evenDensity (12+h) ≤ evenDensity 12 - 0.6389*h := by
  rcases hh.eq_or_lt with he | hp
  · subst h
    simp
  have hsec := hc.slope_anti_adjacent (x := 11.3) (y := 12) (z := 12+h)
    (by norm_num) (show (0 : ℝ) ≤ 12+h by linarith) (by norm_num) (by linarith)
  have hbase : (evenDensity 12 - evenDensity 11.3) / (12 - 11.3) ≤ -0.6389 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12 - 11.3)).2
    linarith
  have hend := (div_le_iff₀ (by linarith : (0 : ℝ) < 12 + h - 12)).1 (hsec.trans hbase)
  linarith

theorem windingContinuation (evenDensity oddDensity : ℝ → ℝ)
    (hc : ConcaveOn ℝ (Set.Ici 0) evenDensity)
    (hleft : -(29333221/6000000 : ℝ) ≤ evenDensity 11.3)
    (hright : evenDensity 12 ≤ -5.33611)
    (hgap : 0.5584 ≤ oddDensity 12 - evenDensity 12)
    {h : ℝ} (hh : 0 ≤ h)
    (hodd : oddDensity 12 - h ≤ oddDensity (12 + h)) :
    0.5584 - 0.3611 * h ≤ oddDensity (12 + h) - evenDensity (12 + h) := by
  linarith [evenSupport evenDensity hc hleft hright hh]

theorem continuationFloor {w h : ℝ} (hh : h ≤ 1.54) (hw : 0.5584 - 0.3611 * h ≤ w) :
    (0.002306 : ℝ) ≤ w := by linarith

/-- A chord for the odd density lies above the affine even-density upper
bound plus a common endpoint margin throughout the interval. -/
theorem chordFloor (oddDensity : ℝ → ℝ) (hc : ConcaveOn ℝ Set.univ oddDensity)
    {a b intercept slope floor t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (ha : intercept + slope * a + floor ≤ oddDensity a)
    (hb : intercept + slope * b + floor ≤ oddDensity b) :
    intercept + slope * ((1-t)*a+t*b) + floor ≤ oddDensity ((1-t)*a+t*b) := by
  have h := hc.2 (Set.mem_univ a) (Set.mem_univ b)
    (sub_nonneg.mpr ht') ht (show 1-t+t=1 by ring)
  simp only [smul_eq_mul] at h
  linarith only [h, mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht'),
    mul_le_mul_of_nonneg_left hb ht]

/-- Rational anchors rounded down from the two implementations, including
the largest-coupling positive anchor used in the manuscript. -/
theorem highEndpointMargins :
    (0.0517 : ℚ) ≤ -9.555414 / 2 + 5.33611 ∧
    (0.0517 : ℚ) ≤ -20.791110 / 2 + 5.33611 + 0.6389 * (20 - 12) := by
  norm_num

theorem windingToTwenty (p m : ℝ → ℝ)
    (hp : ConcaveOn ℝ (Set.Ici 0) p) (hm : ConcaveOn ℝ Set.univ m)
    (hp11 : -(29333221/6000000 : ℝ) ≤ p 11.3) (hp12 : p 12 ≤ -5.33611)
    (hm12 : -9.555414 / 2 ≤ m 12) (hm20 : -20.791110 / 2 ≤ m 20)
    {x : ℝ} (hx : 12 ≤ x) (hx' : x ≤ 20) : 0.0517 ≤ m x - p x := by
  let t := (x-12)/8
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht' : t ≤ 1 := by dsimp [t]; linarith
  have heq : (1-t)*12+t*20=x := by dsimp [t]; ring
  have ho := chordFloor m hm (a := 12) (b := 20) (intercept := -5.33611+0.6389*12)
    (slope := -0.6389) (floor := 0.0517) ht ht' (by linarith) (by linarith)
  rw [heq] at ho
  have he := evenSupport p hp hp11 hp12 (sub_nonneg.mpr hx)
  rw [show 12+(x-12)=x by ring] at he
  linarith

#print axioms GaugeGaps.Full.full_gap_gt_one
#print axioms GaugeGaps.Lemma1.trace_mul_inv_su2
#print axioms anchorRows
#print axioms windingContinuation
#print axioms continuationFloor
#print axioms chordFloor
#print axioms highEndpointMargins
#print axioms windingToTwenty

end GaugeGaps.WindingContinuation
