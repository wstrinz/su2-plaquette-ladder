import CertifiedGaps.Ring.Gap
import CertifiedGaps.Spectral.Counting
import CertifiedGaps.Spectral.Schur
import GaugeGaps.Z3GaugeHiggs

/-!
# The `ℤ₃` gauge–Higgs ring Hamiltonian on vectors

For the model `Z3GaugeHiggs.model e κ` this file writes the action of the ring Hamiltonian on a
vector in the basis of link configurations `σ : Fin L → Fin 3`:

`(H x)(σ) = E(σ) x(σ) - (e/2) ∑ⱼ [x(σ + δⱼ) + x(σ + 2δⱼ)]
              - (1/2) ∑ⱼ [x(σ + δⱼ + 2δⱼ₊₁) + x(σ + 2δⱼ + δⱼ₊₁)]`,

with the classical energy `E(σ) = -(κ/2) ∑ⱼ D(σⱼ)`, `D = diag(2, -1, -1)`. Every off-diagonal term
is a permutation of the configurations, so the form of `H` is at least that of `E - (e + 1) L`
(`re_quadratic_ge`), and at most one eigenvalue lies below `-κL + 3κ/2 - (e + 1)L`
(`card_low_le`): the only configuration below that classical energy is `σ = 0`.

The structure follows `SeedKernel/Ising/Hamiltonian.lean` of the CertifiedGaps library.
-/

open Matrix Complex CertifiedGaps CertifiedGaps.Spectral

namespace GaugeGaps.Z3Seed

open GaugeGaps.Z3GaugeHiggs

variable {L : ℕ}

/-- `2 Re χ(w)`: the diagonal of `D`. -/
def dR (a : Fin 3) : ℝ := if a = 0 then 2 else -1

/-- The classical energy `E(σ) = -(κ/2) ∑ⱼ D(σⱼ)` of a configuration. -/
noncomputable def diagE (κ : ℝ) (σ : Fin L → Fin 3) : ℝ := -(κ / 2) * ∑ j, dR (σ j)

/-- The configuration with the link `j` shifted by `a`. -/
def shiftAt (j : Fin L) (a : Fin 3) (σ : Fin L → Fin 3) : Fin L → Fin 3 :=
  Function.update σ j (σ j + a)

theorem shiftAt_zero (j : Fin L) (σ : Fin L → Fin 3) : shiftAt j 0 σ = σ := by
  simp [shiftAt]

theorem shiftAt_shiftAt (j : Fin L) (a b : Fin 3) (σ : Fin L → Fin 3) :
    shiftAt j a (shiftAt j b σ) = shiftAt j (b + a) σ := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [shiftAt, add_assoc]
  · simp [shiftAt, hi]

/-- Shifting a link as a permutation of the configurations. -/
def shiftPerm (j : Fin L) (a : Fin 3) : Equiv.Perm (Fin L → Fin 3) where
  toFun := shiftAt j a
  invFun := shiftAt j (-a)
  left_inv σ := by rw [shiftAt_shiftAt, add_neg_cancel, shiftAt_zero]
  right_inv σ := by rw [shiftAt_shiftAt, neg_add_cancel, shiftAt_zero]

/-! ### The local matrices -/

theorem oc_apply_add (e κ : ℝ) (s a : Fin 3) :
    (model e κ).oc s (s + a) =
      if a = 0 then ((-(κ / 2) * dR s : ℝ) : ℂ) else ((-(e / 2) : ℝ) : ℂ) := by
  fin_cases s <;> fin_cases a <;> simp [RPRing.oc, model, castM, Aq, Dq, dR]

theorem Cc_zero_apply (e κ : ℝ) (s c : Fin 3) :
    (model e κ).Cc 0 s c = ((Aq s c : ℤ) : ℂ) / 2 := by
  change ((((1 / 2 : ℝ) • castM Aq) s c : ℝ) : ℂ) = _
  rw [Matrix.smul_apply, castM_apply, smul_eq_mul]
  push_cast; ring

theorem Cc_one_apply (e κ : ℝ) (s c : Fin 3) :
    (model e κ).Cc 1 s c = ((Bq s c : ℤ) : ℂ) / 2 := by
  change ((((1 / 2 : ℝ) • castM Bq) s c : ℝ) : ℂ) = _
  rw [Matrix.smul_apply, castM_apply, smul_eq_mul]
  push_cast; ring

theorem Dc_zero (e κ : ℝ) : (model e κ).Dc 0 = (model e κ).Cc 0 := by
  have h : (model e κ).refl * (model e κ).C 0 * (model e κ).refl = (model e κ).C 0 := by
    change castM Fq * ((1 / 2 : ℝ) • castM Aq) * castM Fq = (1 / 2 : ℝ) • castM Aq
    rw [Matrix.mul_smul, Matrix.smul_mul, castM_conj, Fq_Aq]
  calc (model e κ).Dc 0
      = ((model e κ).refl * (model e κ).C 0 * (model e κ).refl).map Complex.ofRealHom := by
        rw [Matrix.map_mul, Matrix.map_mul]; rfl
    _ = (model e κ).Cc 0 := by rw [h]; rfl

theorem Dc_one (e κ : ℝ) : (model e κ).Dc 1 = -(model e κ).Cc 1 := by
  have h : (model e κ).refl * (model e κ).C 1 * (model e κ).refl = -(model e κ).C 1 := by
    change castM Fq * ((1 / 2 : ℝ) • castM Bq) * castM Fq = -((1 / 2 : ℝ) • castM Bq)
    rw [Matrix.mul_smul, Matrix.smul_mul, castM_conj, Fq_Bq, castM_neg, smul_neg]
  calc (model e κ).Dc 1
      = ((model e κ).refl * (model e κ).C 1 * (model e κ).refl).map Complex.ofRealHom := by
        rw [Matrix.map_mul, Matrix.map_mul]; rfl
    _ = -(model e κ).Cc 1 := by
        rw [h]; ext i j; simp [RPRing.Cc]

theorem bondMatrix_apply (e κ : ℝ) (s t c d : Fin 3) :
    (model e κ).bondMatrix (s, t) (c, d) =
      -(((Aq s c * Aq t d - Bq s c * Bq t d : ℤ) : ℂ) / 4) := by
  simp only [RPRing.bondMatrix, Fin.sum_univ_two, Dc_zero, Dc_one, Matrix.neg_apply,
    Matrix.add_apply, kroneckerMap_apply, Cc_zero_apply, Cc_one_apply]
  push_cast; ring

theorem bondZ_add : ∀ s t a b : Fin 3,
    Aq s (s + a) * Aq t (t + b) - Bq s (s + a) * Bq t (t + b) =
      if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then 2 else 0 := by decide

theorem bondMatrix_apply_add (e κ : ℝ) (s t a b : Fin 3) :
    (model e κ).bondMatrix (s, t) (s + a, t + b) =
      if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then ((-(1 / 2) : ℝ) : ℂ) else 0 := by
  rw [bondMatrix_apply, bondZ_add]
  split_ifs <;> push_cast <;> norm_num

/-! ### The Hamiltonian on a vector -/

theorem site_mulVec_apply (e κ : ℝ) (j : Fin L) (x : (Fin L → Fin 3) → ℂ) (σ : Fin L → Fin 3) :
    ((model e κ).site L j *ᵥ x) σ =
      ((-(κ / 2) * dR (σ j) : ℝ) : ℂ) * x σ -
        ((e / 2 : ℝ) : ℂ) * (x (shiftAt j 1 σ) + x (shiftAt j 2 σ)) := by
  rw [RPRing.site, siteOp_mulVec_apply,
    ← Equiv.sum_comp (Equiv.addLeft (σ j))
      (fun b ↦ (model e κ).oc (σ j) b * x (Function.update σ j b)),
    Fin.sum_univ_three]
  simp only [Equiv.coe_addLeft, oc_apply_add, shiftAt]
  simp
  ring

theorem bondOp_mulVec_apply {j k : Fin L} (hjk : j ≠ k)
    (B : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (x : (Fin L → Fin 3) → ℂ)
    (σ : Fin L → Fin 3) :
    (bondOp j k B *ᵥ x) σ =
      ∑ p : Fin 3 × Fin 3,
        B (σ j, σ k) p * x (Function.update (Function.update σ j p.1) k p.2) := by
  simp only [mulVec, dotProduct, bondOp, of_apply, ite_mul, zero_mul]
  rw [sum_ite_agree_off hjk]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [Function.update_self, Function.update_of_ne hjk]

theorem bond_mulVec_apply (e κ : ℝ) (hL : 2 ≤ L) (j : Fin L) (x : (Fin L → Fin 3) → ℂ)
    (σ : Fin L → Fin 3) :
    ((model e κ).bond L j *ᵥ x) σ =
      -(((1 / 2 : ℝ) : ℂ) * (x (shiftAt (finRotate L j) 2 (shiftAt j 1 σ)) +
        x (shiftAt (finRotate L j) 1 (shiftAt j 2 σ)))) := by
  have hjk : j ≠ finRotate L j := ne_finRotate hL j
  have h (a b : Fin 3) : Function.update (Function.update σ j (σ j + a)) (finRotate L j)
      (σ (finRotate L j) + b) = shiftAt (finRotate L j) b (shiftAt j a σ) := by
    unfold shiftAt
    rw [Function.update_of_ne hjk.symm]
  rw [RPRing.bond, bondOp_mulVec_apply hjk,
    ← Equiv.sum_comp ((Equiv.addLeft (σ j)).prodCongr (Equiv.addLeft (σ (finRotate L j)))) _,
    Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, Equiv.prodCongr_apply, Equiv.coe_addLeft, Prod.map_apply,
    bondMatrix_apply_add, h]
  simp
  ring

/-- **The Hamiltonian on a vector.** -/
theorem hamiltonian_mulVec_apply (e κ : ℝ) (hL : 2 ≤ L) (x : (Fin L → Fin 3) → ℂ)
    (σ : Fin L → Fin 3) :
    ((model e κ).hamiltonian L *ᵥ x) σ =
      (diagE κ σ : ℂ) * x σ -
        ((e / 2 : ℝ) : ℂ) * ∑ j, (x (shiftAt j 1 σ) + x (shiftAt j 2 σ)) -
        ((1 / 2 : ℝ) : ℂ) * ∑ j, (x (shiftAt (finRotate L j) 2 (shiftAt j 1 σ)) +
          x (shiftAt (finRotate L j) 1 (shiftAt j 2 σ))) := by
  have hd : ∑ j : Fin L, ((-(κ / 2) * dR (σ j) : ℝ) : ℂ) * x σ = (diagE κ σ : ℂ) * x σ := by
    rw [← Finset.sum_mul, diagE, Finset.mul_sum, Complex.ofReal_sum]
  rw [RPRing.hamiltonian, add_mulVec, sum_mulVec, sum_mulVec, Pi.add_apply, Finset.sum_apply,
    Finset.sum_apply]
  simp only [site_mulVec_apply, bond_mulVec_apply e κ hL, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [hd]
  ring

/-! ### Comparison with the classical energies -/

/-- A permutation of the configurations gives a term of size at most `‖x‖²`. -/
theorem perm_term_le (π : Equiv.Perm (Fin L → Fin 3)) (x : (Fin L → Fin 3) → ℂ) :
    ∑ σ, (star (x σ) * x (π σ)).re ≤ nsq x := by
  have hperm : nsq (x ∘ π) = nsq x := by
    simp only [nsq_eq_sum, Function.comp_apply]
    exact Equiv.sum_comp π fun σ ↦ ‖x σ‖ ^ 2
  have hcs := re_dotProduct_sq_le x (x ∘ π)
  rw [hperm, ← sq] at hcs
  have h := le_of_sq_le_sq hcs (nsq_nonneg x)
  simpa [dotProduct, Complex.re_sum] using h

theorem re_star_mul_combo (c z S B : ℂ) (D a b : ℝ) :
    (star c * ((D : ℂ) * z - (a : ℂ) * S - (b : ℂ) * B)).re =
      D * (star c * z).re - a * (star c * S).re - b * (star c * B).re := by
  have h : star c * ((D : ℂ) * z - (a : ℂ) * S - (b : ℂ) * B) =
      (D : ℂ) * (star c * z) - (a : ℂ) * (star c * S) - (b : ℂ) * (star c * B) := by ring
  rw [h, Complex.sub_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]

theorem star_mul_self_re (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **Comparison with the classical energies.** For `e ≥ 0` and `L ≥ 2`,
`Re ⟪x, H x⟫ ≥ ∑_σ (E(σ) - (e + 1) L) |x(σ)|²`. -/
theorem re_quadratic_ge (e κ : ℝ) (he : 0 ≤ e) (hL : 2 ≤ L) (x : (Fin L → Fin 3) → ℂ) :
    ∑ σ, (diagE κ σ - (e + 1) * L) * ‖x σ‖ ^ 2 ≤ qform ((model e κ).hamiltonian L) x := by
  have hσ (σ : Fin L → Fin 3) :
      (star (x σ) * ((model e κ).hamiltonian L *ᵥ x) σ).re =
        diagE κ σ * ‖x σ‖ ^ 2 -
          (e / 2) * ∑ j, ((star (x σ) * x (shiftAt j 1 σ)).re +
            (star (x σ) * x (shiftAt j 2 σ)).re) -
          (1 / 2) * ∑ j, ((star (x σ) * x (shiftAt (finRotate L j) 2 (shiftAt j 1 σ))).re +
            (star (x σ) * x (shiftAt (finRotate L j) 1 (shiftAt j 2 σ))).re) := by
    rw [hamiltonian_mulVec_apply e κ hL, re_star_mul_combo, star_mul_self_re, Finset.mul_sum,
      Finset.mul_sum, Complex.re_sum, Complex.re_sum]
    simp only [mul_add, Complex.add_re]
  have h1 : ∑ σ, ∑ j, ((star (x σ) * x (shiftAt j 1 σ)).re +
      (star (x σ) * x (shiftAt j 2 σ)).re) ≤ 2 * L * nsq x := by
    rw [Finset.sum_comm]
    calc ∑ j : Fin L, ∑ σ, ((star (x σ) * x (shiftAt j 1 σ)).re +
          (star (x σ) * x (shiftAt j 2 σ)).re)
        ≤ ∑ _j : Fin L, (nsq x + nsq x) := Finset.sum_le_sum fun j _ ↦ by
          rw [Finset.sum_add_distrib]
          exact add_le_add (perm_term_le (shiftPerm j 1) x) (perm_term_le (shiftPerm j 2) x)
      _ = 2 * L * nsq x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h2 : ∑ σ, ∑ j, ((star (x σ) * x (shiftAt (finRotate L j) 2 (shiftAt j 1 σ))).re +
      (star (x σ) * x (shiftAt (finRotate L j) 1 (shiftAt j 2 σ))).re) ≤ 2 * L * nsq x := by
    rw [Finset.sum_comm]
    calc ∑ j : Fin L, ∑ σ, ((star (x σ) * x (shiftAt (finRotate L j) 2 (shiftAt j 1 σ))).re +
          (star (x σ) * x (shiftAt (finRotate L j) 1 (shiftAt j 2 σ))).re)
        ≤ ∑ _j : Fin L, (nsq x + nsq x) := Finset.sum_le_sum fun j _ ↦ by
          rw [Finset.sum_add_distrib]
          exact add_le_add
            (perm_term_le ((shiftPerm j 1).trans (shiftPerm (finRotate L j) 2)) x)
            (perm_term_le ((shiftPerm j 2).trans (shiftPerm (finRotate L j) 1)) x)
      _ = 2 * L * nsq x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hexp : qform ((model e κ).hamiltonian L) x =
      ∑ σ, diagE κ σ * ‖x σ‖ ^ 2 -
        (e / 2) * ∑ σ, ∑ j, ((star (x σ) * x (shiftAt j 1 σ)).re +
          (star (x σ) * x (shiftAt j 2 σ)).re) -
        (1 / 2) * ∑ σ, ∑ j, ((star (x σ) * x (shiftAt (finRotate L j) 2 (shiftAt j 1 σ))).re +
          (star (x σ) * x (shiftAt (finRotate L j) 1 (shiftAt j 2 σ))).re) := by
    rw [qform, RCLike.re_to_complex, dotProduct, Complex.re_sum]
    simp only [Pi.star_apply, hσ, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hlhs : ∑ σ, (diagE κ σ - (e + 1) * L) * ‖x σ‖ ^ 2 =
      ∑ σ, diagE κ σ * ‖x σ‖ ^ 2 - (e + 1) * L * nsq x := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, nsq_eq_sum]
  rw [hexp, hlhs]
  have hn := nsq_nonneg x
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ e / 2), h2]

/-! ### Counting -/

/-- Every configuration other than `σ = 0` has classical energy at least `-κL + 3κ/2`. -/
theorem diagE_ge (κ : ℝ) (hκ : 0 ≤ κ) (σ : Fin L → Fin 3) (hσ : σ ≠ fun _ ↦ 0) :
    -(κ * L) + 3 * κ / 2 ≤ diagE κ σ := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, σ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hσ (funext h)
  have h2 : ∀ a : Fin 3, 0 ≤ 2 - dR a := by
    intro a; unfold dR; split_ifs <;> norm_num
  have h3 : (3 : ℝ) ≤ ∑ j, (2 - dR (σ j)) := by
    have h := Finset.single_le_sum (f := fun j ↦ 2 - dR (σ j)) (fun j _ ↦ h2 (σ j))
      (Finset.mem_univ j₀)
    have h0 : 2 - dR (σ j₀) = 3 := by rw [dR, ite_eq_right hj₀]; norm_num
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h3
  unfold diagE
  nlinarith [mul_nonneg hκ (by linarith : (0 : ℝ) ≤ L * 2 - ∑ j, dR (σ j) - 3)]

/-- **Counting.** At most one eigenvalue of the ring lies below `-κL + 3κ/2 - (e + 1)L`. -/
theorem card_low_le (e κ : ℝ) (he : 0 ≤ e) (hκ : 0 ≤ κ) (hL : 2 ≤ L) :
    (Finset.univ.filter fun i ↦
      (model e κ).spectrum L i < -(κ * L) + 3 * κ / 2 - (e + 1) * L).card ≤ 1 := by
  classical
  refine le_trans (eigCount_le_card_of_vanishing ((model e κ).hamiltonian_isHermitian L)
    ({fun _ ↦ 0} : Finset (Fin L → Fin 3)) fun x hx ↦ ?_) (by simp)
  refine le_trans ?_ (re_quadratic_ge e κ he hL x)
  rw [nsq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ ↦ ?_
  by_cases hσ : σ = fun _ ↦ 0
  · have h0 : x σ = 0 := hx σ (by simp [hσ])
    simp [h0]
  · exact mul_le_mul_of_nonneg_right (by linarith [diagE_ge κ hκ σ hσ]) (sq_nonneg _)

end GaugeGaps.Z3Seed
