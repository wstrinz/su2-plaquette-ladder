import Mathlib.Tactic

/- Assuming the spectral chord lower bound and the affine trial upper bound,
the two outward-rounded endpoint values imply the winding-cost floor. -/
namespace GaugeGaps.RefinedTension

theorem refined_winding_floor {t odd even : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1)
    (ho : (1-t)*(-36161741/1000000/2) + t*(-39523661/1000000/2) ≤ odd)
    (he : even ≤ (1-t)*(-152359/8307) + t*(-165346/8307)) :
    57/400 ≤ odd-even := by
  have ha : (57/400 : ℝ) ≤ -36161741/1000000/2 + 152359/8307 := by norm_num
  have hb : (57/400 : ℝ) ≤ -39523661/1000000/2 + 165346/8307 := by norm_num
  nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr ha),
    mul_nonneg h₀ (sub_nonneg.mpr hb)]

#print axioms refined_winding_floor
end GaugeGaps.RefinedTension
