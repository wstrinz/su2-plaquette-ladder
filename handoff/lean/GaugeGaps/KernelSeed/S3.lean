import GaugeGaps.KernelSeed.Seed
import GaugeGaps.S3GaugeHiggs

/-!
# Integer tables of the `S₃` gauge–Higgs chain

For integer couplings `e`, `κ` the local matrices of `S3GaugeHiggs.model e κ` are
`6 o = -2 e ∑_h L_h - 3 κ χ` and `6 h = -2 ∑_h R_h ⊗ L_h` divided by `6`, with `L_h = F R_h F`.
-/

open Matrix Complex CertifiedGaps

namespace GaugeGaps.S3Seed

open GaugeGaps.S3GaugeHiggs GaugeGaps.KernelSeed


/-- The left shifts as explicit matrices, for the checker. -/
def LqT : Fin 3 → Matrix (Fin 6) (Fin 6) ℤ := ![
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0],
  !![0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0],
  !![0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0]]

theorem LqT_eq : ∀ h, LqT h = Fq * Rq h * Fq := by decide +kernel

/-- The integer tables at integer couplings. -/
def tables (e κ : ℤ) : IntRing 6 where
  den := 6
  o a b := -(2 * e * Lsum a b) - 3 * κ * Dq a b
  b a b c f := -2 * ∑ h : Fin 3, Rq h a c * LqT h b f

theorem Cc_apply (e κ : ℝ) (α : Fin 3 × Fin 3) (a c : Fin 6) :
    (model e κ).Cc α a c = ((Rq α.1 a c : ℤ) : ℂ) / 3 := by
  change ((((1 / 3 : ℝ) • castM (Rq α.1)) a c : ℝ) : ℂ) = _
  rw [Matrix.smul_apply, castM_apply, smul_eq_mul]
  push_cast
  ring

theorem Dc_eq (e κ : ℝ) (α : Fin 3 × Fin 3) :
    (model e κ).Dc α = ((1 / 3 : ℝ) • castM (LqT α.1)).map Complex.ofRealHom := by
  have h : (model e κ).refl * (model e κ).C α * (model e κ).refl =
      (1 / 3 : ℝ) • castM (LqT α.1) := by
    change castM Fq * ((1 / 3 : ℝ) • castM (Rq α.1)) * castM Fq = _
    rw [Matrix.mul_smul, Matrix.smul_mul, castM_conj, LqT_eq]
  calc (model e κ).Dc α
      = ((model e κ).refl * (model e κ).C α * (model e κ).refl).map Complex.ofRealHom := by
        rw [Matrix.map_mul, Matrix.map_mul]; rfl
    _ = _ := by rw [h]

theorem Dc_apply (e κ : ℝ) (α : Fin 3 × Fin 3) (b f : Fin 6) :
    (model e κ).Dc α b f = ((LqT α.1 b f : ℤ) : ℂ) / 3 := by
  rw [Dc_eq]
  change ((((1 / 3 : ℝ) • castM (LqT α.1)) b f : ℝ) : ℂ) = _
  rw [Matrix.smul_apply, castM_apply, smul_eq_mul]
  push_cast
  ring

/-- The model at integer couplings has the integer tables `tables e κ`. -/
theorem represents {e κ : ℝ} (eZ κZ : ℤ) (he : e = eZ) (hκ : κ = κZ) :
    Represents (model e κ) (tables eZ κZ) where
  den_pos := by change (0 : ℤ) < 6; norm_num
  oc a b := by
    subst he hκ
    change (((-((eZ : ℝ) / 3) • castM Lsum - ((κZ : ℝ) / 2) • castM Dq) a b : ℝ) : ℂ) =
      ((-(2 * eZ * Lsum a b) - 3 * κZ * Dq a b : ℤ) : ℂ) / ((6 : ℤ) : ℂ)
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, castM_apply, castM_apply,
      smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  bond a b c f := by
    change (model e κ).bondMatrix (a, b) (c, f) =
      ((-2 * ∑ h : Fin 3, Rq h a c * LqT h b f : ℤ) : ℂ) / ((6 : ℤ) : ℂ)
    simp only [RPRing.bondMatrix, Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.neg_apply,
      Matrix.add_apply, kroneckerMap_apply, Cc_apply, Dc_apply]
    push_cast
    ring

end GaugeGaps.S3Seed
