import CertifiedGaps.Ring.Gap
import CertifiedGaps.Spectral.Counting

/-!
# A Gershgorin lower bound for the form of a ring Hamiltonian

For a Hermitian matrix `M`, `Re ⟪x, M x⟫ ≥ ∑ᵢ (Mᵢᵢ - ∑_{k ≠ i} ‖Mᵢₖ‖) ‖xᵢ‖²` (`qform_ge_gershgorin`).
Applied to each bond and on-site term of a reflection-positive ring this gives
`Re ⟪x, H_L x⟫ ≥ ∑_σ g(σ) ‖x(σ)‖²` with the *local* function
`g(σ) = ∑ⱼ g_bond(σⱼ, σⱼ₊₁) + ∑ⱼ g_site(σⱼ)` (`qform_hamiltonian_ge`), where `g_site` and `g_bond` are
the Gershgorin lower discs of the one-site and two-site matrices. No structure of the model is used.
-/

open Matrix Complex CertifiedGaps CertifiedGaps.Spectral

set_option linter.unusedSectionVars false

namespace GaugeGaps.KernelSeed

section Form

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The norm of an off-diagonal entry, and `0` on the diagonal. -/
noncomputable def offNorm (M : Matrix n n ℂ) (i k : n) : ℝ := if i = k then 0 else ‖M i k‖

theorem offNorm_self (M : Matrix n n ℂ) (i : n) : offNorm M i i = 0 := by simp [offNorm]

theorem offNorm_of_ne (M : Matrix n n ℂ) {i k : n} (h : i ≠ k) : offNorm M i k = ‖M i k‖ := by
  simp [offNorm, h]

theorem offNorm_symm {M : Matrix n n ℂ} (hM : M.IsHermitian) (i k : n) :
    offNorm M i k = offNorm M k i := by
  by_cases h : i = k
  · subst h; rfl
  · rw [offNorm_of_ne M h, offNorm_of_ne M (Ne.symm h), ← hM.apply i k, norm_star]

/-- **Gershgorin bound for the form.** -/
theorem qform_ge_gershgorin {M : Matrix n n ℂ} (hM : M.IsHermitian) (x : n → ℂ) :
    ∑ i, ((M i i).re - ∑ k, offNorm M i k) * ‖x i‖ ^ 2 ≤ qform M x := by
  have hq : qform M x = ∑ i, ∑ k, (star (x i) * (M i k * x k)).re := by
    simp only [qform, RCLike.re_to_complex, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum,
      Complex.re_sum]
  have hterm (i k : n) :
      (if i = k then (M i i).re * ‖x i‖ ^ 2 else 0) -
        (offNorm M i k * ‖x i‖ ^ 2 + offNorm M i k * ‖x k‖ ^ 2) / 2 ≤
          (star (x i) * (M i k * x k)).re := by
    by_cases h : i = k
    · subst h
      have e : star (x i) * (M i i * x i) = M i i * ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_left_comm, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
      rw [e, Complex.re_mul_ofReal, offNorm_self]
      simp
    · have h1 : |(star (x i) * (M i k * x k)).re| ≤ ‖x i‖ * (‖M i k‖ * ‖x k‖) := by
        have h0 := Complex.abs_re_le_norm (star (x i) * (M i k * x k))
        rwa [norm_mul, norm_mul, norm_star] at h0
      have h2 := neg_abs_le ((star (x i) * (M i k * x k)).re)
      have h3 : ‖x i‖ * (‖M i k‖ * ‖x k‖) ≤
          (‖M i k‖ * ‖x i‖ ^ 2 + ‖M i k‖ * ‖x k‖ ^ 2) / 2 := by
        nlinarith [mul_nonneg (norm_nonneg (M i k)) (sq_nonneg (‖x i‖ - ‖x k‖))]
      rw [offNorm_of_ne M h]
      simp only [h, ↓reduceIte]
      linarith
  have hswap : ∑ i, ∑ k, offNorm M i k * ‖x k‖ ^ 2 = ∑ i, ∑ k, offNorm M i k * ‖x i‖ ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by
      rw [offNorm_symm hM]
  have hhalf : ∑ i, ∑ k, (offNorm M i k * ‖x i‖ ^ 2 + offNorm M i k * ‖x k‖ ^ 2) / 2 =
      ∑ i, ∑ k, offNorm M i k * ‖x i‖ ^ 2 := by
    calc ∑ i, ∑ k, (offNorm M i k * ‖x i‖ ^ 2 + offNorm M i k * ‖x k‖ ^ 2) / 2
        = (∑ i, ∑ k, offNorm M i k * ‖x i‖ ^ 2 + ∑ i, ∑ k, offNorm M i k * ‖x k‖ ^ 2) / 2 := by
          simp only [← Finset.sum_div, Finset.sum_add_distrib]
      _ = ∑ i, ∑ k, offNorm M i k * ‖x i‖ ^ 2 := by rw [hswap]; ring
  have hsum : ∑ i, ((M i i).re - ∑ k, offNorm M i k) * ‖x i‖ ^ 2 =
      ∑ i, ∑ k, ((if i = k then (M i i).re * ‖x i‖ ^ 2 else 0) -
        (offNorm M i k * ‖x i‖ ^ 2 + offNorm M i k * ‖x k‖ ^ 2) / 2) := by
    simp only [sub_mul, Finset.sum_mul, Finset.sum_sub_distrib]
    rw [hhalf]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hq, hsum]
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun k _ ↦ hterm i k

end Form

/-! ### One-site and two-site terms on a ring -/

section Ring

variable {d : Type} [Fintype d] [DecidableEq d] {L : ℕ}

/-- The Gershgorin lower disc of a one-site matrix at the letter `a`. -/
noncomputable def gSite (A : Matrix d d ℂ) (a : d) : ℝ := (A a a).re - ∑ b, offNorm A a b

/-- The Gershgorin lower disc of a two-site matrix at the pair `q`. -/
noncomputable def gBond (B : Matrix (d × d) (d × d) ℂ) (q : d × d) : ℝ :=
  (B q q).re - ∑ p, offNorm B q p

theorem siteOp_diag (j : Fin L) (A : Matrix d d ℂ) (σ : Fin L → d) :
    siteOp j A σ σ = A (σ j) (σ j) := by
  rw [siteOp_apply]; simp

theorem siteOp_row (j : Fin L) (A : Matrix d d ℂ) (σ : Fin L → d) :
    ∑ τ, offNorm (siteOp j A) σ τ = ∑ b, offNorm A (σ j) b := by
  have h (τ : Fin L → d) : offNorm (siteOp j A) σ τ =
      if ∀ i, i ≠ j → σ i = τ i then (if σ = τ then 0 else ‖A (σ j) (τ j)‖) else 0 := by
    unfold offNorm
    rw [siteOp_apply]
    by_cases hst : σ = τ
    · subst hst; simp
    · simp only [hst, ↓reduceIte]
      split_ifs <;> simp
  simp only [h]
  rw [sum_ite_agree_off_site]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Function.update_self]
  by_cases hb : σ j = b
  · have hσ : σ = Function.update σ j b := by rw [← hb, Function.update_eq_self]
    simp [offNorm, hb, ← hσ]
  · have hσ : σ ≠ Function.update σ j b := fun h ↦ hb (by
      have h1 := congrFun h j
      rwa [Function.update_self] at h1)
    simp [offNorm, hb, hσ]

theorem qform_siteOp_ge (j : Fin L) {A : Matrix d d ℂ} (hA : A.IsHermitian)
    (x : (Fin L → d) → ℂ) :
    ∑ σ, gSite A (σ j) * ‖x σ‖ ^ 2 ≤ qform (siteOp j A) x := by
  have h := qform_ge_gershgorin (siteOp_isHermitian j hA) x
  simpa only [siteOp_row, siteOp_diag, gSite] using h

theorem bondOp_diag (j k : Fin L) (B : Matrix (d × d) (d × d) ℂ) (σ : Fin L → d) :
    bondOp j k B σ σ = B (σ j, σ k) (σ j, σ k) := by
  simp [bondOp]

theorem bondOp_row {j k : Fin L} (hjk : j ≠ k) (B : Matrix (d × d) (d × d) ℂ)
    (σ : Fin L → d) :
    ∑ τ, offNorm (bondOp j k B) σ τ = ∑ p, offNorm B (σ j, σ k) p := by
  have h (τ : Fin L → d) : offNorm (bondOp j k B) σ τ =
      if ∀ i, i ≠ j → i ≠ k → σ i = τ i then
        (if σ = τ then 0 else ‖B (σ j, σ k) (τ j, τ k)‖) else 0 := by
    unfold offNorm
    simp only [bondOp, of_apply]
    by_cases hst : σ = τ
    · subst hst; simp
    · simp only [hst, ↓reduceIte]
      split_ifs <;> simp
  simp only [h]
  rw [sum_ite_agree_off hjk]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [Function.update_self, Function.update_of_ne hjk]
  by_cases hp : (σ j, σ k) = p
  · have hσ : σ = Function.update (Function.update σ j p.1) k p.2 := by
      rw [← hp]; simp
    simp [offNorm, hp, ← hσ]
  · have hσ : σ ≠ Function.update (Function.update σ j p.1) k p.2 := fun h ↦ hp (by
      have h1 := congrFun h j
      have h2 := congrFun h k
      rw [Function.update_of_ne hjk, Function.update_self] at h1
      rw [Function.update_self] at h2
      exact Prod.ext h1 h2)
    simp [offNorm, hp, hσ]

theorem qform_bondOp_ge {j k : Fin L} (hjk : j ≠ k) {B : Matrix (d × d) (d × d) ℂ}
    (hB : B.IsHermitian) (x : (Fin L → d) → ℂ) :
    ∑ σ, gBond B (σ j, σ k) * ‖x σ‖ ^ 2 ≤ qform (bondOp j k B) x := by
  have h := qform_ge_gershgorin (bondOp_isHermitian j k hB) x
  simpa only [bondOp_row hjk, bondOp_diag, gBond] using h

variable {ι : Type} [Fintype ι] (R : RPRing d ι)

/-- The local Gershgorin function of the ring. -/
noncomputable def gersh (σ : Fin L → d) : ℝ :=
  ∑ j, gBond R.bondMatrix (σ j, σ (finRotate L j)) + ∑ j, gSite R.oc (σ j)

/-- **The form of the ring Hamiltonian is at least that of its local Gershgorin function.** -/
theorem qform_hamiltonian_ge (hL : 2 ≤ L) (x : (Fin L → d) → ℂ) :
    ∑ σ, gersh R σ * ‖x σ‖ ^ 2 ≤ qform (R.hamiltonian L) x := by
  rw [RPRing.hamiltonian, qform_add_left, qform_sum, qform_sum]
  calc ∑ σ, gersh R σ * ‖x σ‖ ^ 2
      = ∑ j, ∑ σ, gBond R.bondMatrix (σ j, σ (finRotate L j)) * ‖x σ‖ ^ 2 +
          ∑ j, ∑ σ, gSite R.oc (σ j) * ‖x σ‖ ^ 2 := by
        simp only [gersh, add_mul, Finset.sum_mul, Finset.sum_add_distrib]
        congr 1 <;> exact Finset.sum_comm
    _ ≤ _ := add_le_add
        (Finset.sum_le_sum fun j _ ↦
          qform_bondOp_ge (ne_finRotate hL j) R.bondMatrix_isHermitian x)
        (Finset.sum_le_sum fun j _ ↦ qform_siteOp_ge j R.oc_isHermitian x)

end Ring

end GaugeGaps.KernelSeed
