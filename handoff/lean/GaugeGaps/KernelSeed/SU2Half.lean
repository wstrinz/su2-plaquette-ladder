import GaugeGaps.KernelSeed.Seed
import GaugeGaps.SU2HalfGaugeHiggs

/-!
# Integer tables of the `SU(2)` gauge–Higgs chain at flux cutoff `1/2`

For integer couplings `e`, `κ` the local matrices of `SU2HalfGaugeHiggs.model e κ` are
`6 o = 6 (e + 2) Π - 3 κ T` and `6 h = -4 ∑_c K^R_c ⊗ K^L_c` divided by `6`.
-/

open Matrix Complex CertifiedGaps

namespace GaugeGaps.SU2HalfSeed

open GaugeGaps.SU2HalfGaugeHiggs GaugeGaps.KernelSeed

/-- The integer tables at integer couplings. -/
def tables (e κ : ℤ) : IntRing 5 where
  den := 6
  o a b := 6 * (e + 2) * Pq a b - 3 * κ * Tq a b
  b a b c f := -4 * ∑ g : Fin 3, KR g a c * KL g b f

theorem Cc_apply (e κ : ℝ) (α : Fin 3 × Fin 3) (a c : Fin 5) :
    (model e κ).Cc α a c = ((copyWeight α.2 : ℝ) : ℂ) * ((KR α.1 a c : ℤ) : ℂ) := by
  change (((copyWeight α.2 • castM (KR α.1)) a c : ℝ) : ℂ) = _
  rw [Matrix.smul_apply, castM_apply, smul_eq_mul]
  push_cast
  rfl

theorem Dc_eq (e κ : ℝ) (α : Fin 3 × Fin 3) :
    (model e κ).Dc α = (copyWeight α.2 • castM (KL α.1)).map Complex.ofRealHom := by
  have h : (model e κ).refl * (model e κ).C α * (model e κ).refl =
      copyWeight α.2 • castM (KL α.1) := by
    change castM Rq * (copyWeight α.2 • castM (KR α.1)) * castM Rq = _
    rw [Matrix.mul_smul, Matrix.smul_mul, castM_conj, Rq_KR]
  calc (model e κ).Dc α
      = ((model e κ).refl * (model e κ).C α * (model e κ).refl).map Complex.ofRealHom := by
        rw [Matrix.map_mul, Matrix.map_mul]; rfl
    _ = _ := by rw [h]

theorem Dc_apply (e κ : ℝ) (α : Fin 3 × Fin 3) (b f : Fin 5) :
    (model e κ).Dc α b f = ((copyWeight α.2 : ℝ) : ℂ) * ((KL α.1 b f : ℤ) : ℂ) := by
  rw [Dc_eq]
  change (((copyWeight α.2 • castM (KL α.1)) b f : ℝ) : ℂ) = _
  rw [Matrix.smul_apply, castM_apply, smul_eq_mul]
  push_cast
  rfl

/-- The model at integer couplings has the integer tables `tables e κ`. -/
theorem represents {e κ : ℝ} (eZ κZ : ℤ) (he : e = eZ) (hκ : κ = κZ) :
    Represents (model e κ) (tables eZ κZ) where
  den_pos := by change (0 : ℤ) < 6; norm_num
  oc a b := by
    subst he hκ
    change (((((eZ : ℝ) + 2) • castM Pq - ((κZ : ℝ) / 2) • castM Tq) a b : ℝ) : ℂ) =
      ((6 * (eZ + 2) * Pq a b - 3 * κZ * Tq a b : ℤ) : ℂ) / ((6 : ℤ) : ℂ)
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, castM_apply, castM_apply,
      smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  bond a b c f := by
    change (model e κ).bondMatrix (a, b) (c, f) =
      ((-4 * ∑ g : Fin 3, KR g a c * KL g b f : ℤ) : ℂ) / ((6 : ℤ) : ℂ)
    simp only [RPRing.bondMatrix, Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.neg_apply,
      Matrix.add_apply, kroneckerMap_apply, Cc_apply, Dc_apply]
    simp [copyWeight]
    ring

end GaugeGaps.SU2HalfSeed
