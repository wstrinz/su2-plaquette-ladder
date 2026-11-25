import GaugeGaps.KernelSeed.Bridge
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Seed purities from kernel checks, for any ring with integer tables

Given `Represents R M`, a residual check of one packed trial vector on a ring and the classical
count `M.classicalCount L cut = 1` locate the ground energy within `1/q` and put every other
eigenvalue above `cut / den` (`lowSpectrum_of_check`). Two such low spectra, on `n` and `2n`
sites, give the seed purities of the purity criterion (`seed_spatial_of`, `seed_thermal_of`) once
two rational inequalities are checked. The proof follows `SeedKernel/Ising/Seed.lean` of the
CertifiedGaps library, with one located eigenvalue instead of two and a Gershgorin count in place
of the classical energies of the Ising chain.
-/

open Real CertifiedGaps

set_option linter.unusedSectionVars false

namespace GaugeGaps.KernelSeed

/-- One eigenvalue in `[a₀, b₀]` and all others at least `ρ`. -/
def LowSpectrum {κ : Type*} (E : κ → ℝ) (a₀ b₀ ρ : ℝ) : Prop :=
  ∃ i₀, a₀ ≤ E i₀ ∧ E i₀ ≤ b₀ ∧ ∀ i, i ≠ i₀ → ρ ≤ E i

theorem sum_exp_ge {κ : Type*} [Fintype κ] {E : κ → ℝ} {a₀ b₀ ρ β : ℝ} (hβ : 0 ≤ β)
    (h : LowSpectrum E a₀ b₀ ρ) : exp (-(β * b₀)) ≤ ∑ i, exp (-(β * E i)) := by
  obtain ⟨i₀, -, hb, -⟩ := h
  calc exp (-(β * b₀)) ≤ exp (-(β * E i₀)) := exp_le_exp.2 (by nlinarith)
    _ ≤ ∑ i, exp (-(β * E i)) :=
      Finset.single_le_sum (f := fun i ↦ exp (-(β * E i))) (fun i _ ↦ (exp_pos _).le)
        (Finset.mem_univ i₀)

theorem sum_exp_le {κ : Type*} [Fintype κ] {E : κ → ℝ} {a₀ b₀ ρ β : ℝ} (hβ : 0 ≤ β)
    (h : LowSpectrum E a₀ b₀ ρ) :
    ∑ i, exp (-(β * E i)) ≤ exp (-(β * a₀)) + Fintype.card κ * exp (-(β * ρ)) := by
  classical
  obtain ⟨i₀, ha, -, hρ⟩ := h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  refine add_le_add (exp_le_exp.2 (by nlinarith)) ?_
  calc ∑ i ∈ Finset.univ.erase i₀, exp (-(β * E i))
      ≤ ∑ _i ∈ Finset.univ.erase i₀, exp (-(β * ρ)) :=
        Finset.sum_le_sum fun i hi ↦
          exp_le_exp.2 (by nlinarith [hρ i (Finset.ne_of_mem_erase hi)])
    _ ≤ Fintype.card κ * exp (-(β * ρ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (Finset.card_le_univ _)

/-- The ratio step (as in `SeedKernel/Ising/Seed.lean`): from `Z₂ ≥ A² e^{-x}`, `Z₁ ≤ A (1 + T)`,
`T ≤ t` to `Z₂ / Z₁² ≥ (1 - x) / (1 + t)²`. -/
theorem ratio_ge {Z₁ Z₂ A x T t : ℝ} (hA : 0 < A) (hZ₁ : 0 < Z₁) (h₁ : Z₁ ≤ A * (1 + T))
    (h₂ : A ^ 2 * exp (-x) ≤ Z₂) (hT : 0 ≤ T) (hTt : T ≤ t) :
    (1 - x) / (1 + t) ^ 2 ≤ Z₂ / Z₁ ^ 2 := by
  have hx : 1 - x ≤ exp (-x) := by linarith [add_one_le_exp (-x)]
  have hZ : Z₁ ^ 2 ≤ A ^ 2 * (1 + t) ^ 2 := by
    rw [← mul_pow]; gcongr; linarith [mul_le_mul_of_nonneg_left hTt hA.le]
  have ht : 0 < 1 + t := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  by_cases hx0 : 1 - x ≤ 0
  · nlinarith [sq_nonneg Z₁, exp_pos (-x), sq_nonneg A, sq_nonneg (1 + t)]
  · calc (1 - x) * Z₁ ^ 2 ≤ (1 - x) * (A ^ 2 * (1 + t) ^ 2) := by gcongr; linarith
      _ ≤ exp (-x) * A ^ 2 * (1 + t) ^ 2 := by nlinarith [sq_nonneg A, sq_nonneg (1 + t)]
      _ ≤ Z₂ * (1 + t) ^ 2 := by nlinarith [sq_nonneg (1 + t)]

theorem exp_neg_nat_le (m : ℕ) : exp (-(m : ℝ)) ≤ 1 / 2.7182818283 ^ m := by
  rw [exp_neg, ← one_div, ← exp_one_pow]
  gcongr
  exact exp_one_gt_d9.le

variable {d : ℕ} [NeZero d] {L : ℕ} {ι : Type} [Fintype ι] {R : RPRing (Fin d) ι}
  {M : IntRing d}

/-- **The low spectrum of a ring** from one residual check and the classical count. -/
theorem lowSpectrum_of_check (h : Represents R M) (S : ℤ) (hS : 0 < S) (hL : 2 ≤ L) (v : ℕ)
    (lam : ℤ) (q : ℕ) (hq : 0 < q) (hdot : 0 < dot d L v)
    (hres : M.residualSq S L v lam * (q : ℤ) ^ 2 ≤ M.den ^ 2 * S ^ 2 * dot d L v) (cut : ℤ)
    (hcount : M.classicalCount L cut = 1)
    (hρ : (lam : ℝ) / (M.den * S) + 1 / q < cut / M.den) :
    LowSpectrum (R.spectrum L) (lam / (M.den * S) - 1 / q) (lam / (M.den * S) + 1 / q)
      (cut / M.den) := by
  classical
  obtain ⟨i₀, h₀⟩ := exists_near_of_check h S hS hL v lam q hq hdot hres
  have h₀' := abs_le.1 h₀
  refine ⟨i₀, by linarith [h₀'.1], by linarith [h₀'.2], fun i hi ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  have hsub : ({i₀, i} : Finset (Fin L → Fin d)) ⊆ Finset.univ.filter fun j ↦
      R.spectrum L j < (cut : ℝ) / M.den := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hj with rfl | rfl
    · linarith [h₀'.2]
    · exact hlt
  have h2 : ({i₀, i} : Finset (Fin L → Fin d)).card = 2 := Finset.card_pair (Ne.symm hi)
  have h3 := (Finset.card_le_card hsub).trans (card_low_le h hL cut)
  omega

/-- `Z ≤ A (1 + d^L e^{-β(ρ - a₀)})` with `A = e^{-β a₀}`. -/
theorem partition_upper {a₀ b₀ ρ β : ℝ} (hβ : 0 ≤ β)
    (h : LowSpectrum (R.spectrum L) a₀ b₀ ρ) :
    R.partitionFunction L β ≤
      exp (-(β * a₀)) * (1 + (d : ℝ) ^ L * exp (-(β * (ρ - a₀)))) := by
  classical
  rw [RPRing.partitionFunction_eq_sum]
  refine (sum_exp_le hβ h).trans (le_of_eq ?_)
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, mul_add, mul_one, ← exp_add,
    mul_left_comm (exp (-(β * a₀))) ((d : ℝ) ^ L)]
  ring_nf

theorem partition_lower {a₀ b₀ ρ β : ℝ} (hβ : 0 ≤ β)
    (h : LowSpectrum (R.spectrum L) a₀ b₀ ρ) :
    exp (-(β * b₀)) ≤ R.partitionFunction L β := by
  rw [RPRing.partitionFunction_eq_sum]
  exact sum_exp_ge hβ h

/-- **The spatial seed** from the low spectra on `n` and `2n` sites and two rational inequalities. -/
theorem seed_spatial_of {n : ℕ} {a₂ b₂ ρ₂ a₄ b₄ ρ₄ β s : ℝ} (hβ : 0 ≤ β)
    (h₂ : LowSpectrum (R.spectrum n) a₂ b₂ ρ₂) (h₄ : LowSpectrum (R.spectrum (2 * n)) a₄ b₄ ρ₄)
    (m : ℕ) (hm : (m : ℝ) ≤ β * (ρ₂ - a₂))
    (hs : 1 - s ≤ (1 - β * (b₄ - 2 * a₂)) / (1 + (d : ℝ) ^ n * (1 / 2.7182818283 ^ m)) ^ 2) :
    1 - s ≤ R.spatialPurity n β := by
  have : Nonempty (Fin d) := ⟨0⟩
  have hu := partition_upper hβ h₂
  have hl := partition_lower hβ h₄
  have hT : (d : ℝ) ^ n * exp (-(β * (ρ₂ - a₂))) ≤ (d : ℝ) ^ n * (1 / 2.7182818283 ^ m) :=
    mul_le_mul_of_nonneg_left
      ((exp_le_exp.2 (by linarith)).trans (exp_neg_nat_le m)) (by positivity)
  have hfinal := ratio_ge (Z₁ := R.partitionFunction n β) (Z₂ := R.partitionFunction (2 * n) β)
    (x := β * (b₄ - 2 * a₂)) (exp_pos (-(β * a₂))) (R.partitionFunction_pos n β) hu ?_
    (by positivity) hT
  · exact hs.trans hfinal
  · refine le_trans (le_of_eq ?_) hl
    rw [← exp_nat_mul, ← exp_add]
    congr 1; push_cast; ring

/-- **The thermal seed** from the low spectrum on `N` sites and two rational inequalities. -/
theorem seed_thermal_of {N : ℕ} {a b ρ β t : ℝ} (hβ : 0 ≤ β)
    (h : LowSpectrum (R.spectrum N) a b ρ) (m : ℕ) (hm : (m : ℝ) ≤ β * (ρ - a))
    (ht : 1 - t ≤ (1 - 2 * β * (b - a)) / (1 + (d : ℝ) ^ N * (1 / 2.7182818283 ^ m)) ^ 2) :
    1 - t ≤ R.thermalPurity N β := by
  have : Nonempty (Fin d) := ⟨0⟩
  have hu := partition_upper hβ h
  have hl := partition_lower (β := 2 * β) (by positivity) h
  have hT : (d : ℝ) ^ N * exp (-(β * (ρ - a))) ≤ (d : ℝ) ^ N * (1 / 2.7182818283 ^ m) :=
    mul_le_mul_of_nonneg_left
      ((exp_le_exp.2 (by linarith)).trans (exp_neg_nat_le m)) (by positivity)
  have hfinal := ratio_ge (Z₁ := R.partitionFunction N β) (Z₂ := R.partitionFunction N (2 * β))
    (x := 2 * β * (b - a)) (exp_pos (-(β * a))) (R.partitionFunction_pos N β) hu ?_
    (by positivity) hT
  · exact ht.trans hfinal
  · refine le_trans (le_of_eq ?_) hl
    rw [← exp_nat_mul, ← exp_add]
    congr 1; push_cast; ring

end GaugeGaps.KernelSeed
