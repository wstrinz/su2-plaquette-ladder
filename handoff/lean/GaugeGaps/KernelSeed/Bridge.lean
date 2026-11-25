import GaugeGaps.KernelSeed.Gershgorin
import GaugeGaps.KernelSeed.Checker

/-!
# From the integer checker to a ring Hamiltonian

For a reflection-positive ring `R` on `Fin d` whose local matrices are the integer tables `M`
divided by `M.den` (`Represents R M`):

* `applyH_encode`: `den (H x)(σ)` is `M.applyH` at the index of `σ`, for `x = vec v`;
* `residualSq_eq`, `exists_near_of_check`: a residual check gives an eigenvalue near `θ`;
* `card_low_le`: the number of eigenvalues below `cut / den` is at most `M.classicalCount`.

Nothing here depends on the model. The structure follows `SeedKernel/Ising/Bridge.lean` and
`Seed.lean` of the CertifiedGaps library.
-/

open Matrix Complex CertifiedGaps CertifiedGaps.Spectral

set_option linter.unusedSectionVars false

namespace GaugeGaps.KernelSeed

theorem foldl_add_eq_sum {β : Type*} [AddCommMonoid β] (f : ℕ → β) (b : β) (N : ℕ) :
    (List.range N).foldl (fun a s ↦ a + f s) b = b + ∑ s ∈ Finset.range N, f s := by
  induction N generalizing b with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp [add_assoc]

theorem sum_blocks {A : Type*} [AddCommMonoid A] (F : ℕ → A) (k m : ℕ) :
    ∑ s ∈ Finset.range (k * m), F s = ∑ c ∈ Finset.range k, ∑ i ∈ Finset.range m, F (c * m + i) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- A residual sum assembled from chunks checked one declaration at a time. -/
theorem residualSq_of_chunks {d : ℕ} [NeZero d] (M : IntRing d) (S : ℤ) (n v : ℕ) (lam : ℤ)
    (k m : ℕ) (hkm : k * m = d ^ n) (vals : List ℤ)
    (h : ∀ c, c < k → M.resChunk S n v lam (c * m) m = vals.getD c 0) :
    M.residualSq S n v lam = ∑ c ∈ Finset.range k, vals.getD c 0 := by
  rw [IntRing.residualSq, ← hkm, foldl_add_eq_sum, zero_add, sum_blocks]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [← h c (Finset.mem_range.1 hc), IntRing.resChunk, foldl_add_eq_sum, zero_add]

/-- A classical count assembled from chunks. -/
theorem classicalCount_of_chunks {d : ℕ} [NeZero d] (M : IntRing d) (n : ℕ) (cut : ℤ)
    (k m : ℕ) (hkm : k * m = d ^ n) (vals : List ℕ)
    (h : ∀ c, c < k → M.countChunk n cut (c * m) m = vals.getD c 0) :
    M.classicalCount n cut = ∑ c ∈ Finset.range k, vals.getD c 0 := by
  rw [IntRing.classicalCount, ← hkm, foldl_add_eq_sum, zero_add, sum_blocks]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [← h c (Finset.mem_range.1 hc), IntRing.countChunk, foldl_add_eq_sum, zero_add]

/-! ### The ring Hamiltonian on a vector -/

section Action

variable {D : Type} [Fintype D] [DecidableEq D] {L : ℕ} {ι : Type} [Fintype ι]

theorem bondOp_mulVec_apply {j k : Fin L} (hjk : j ≠ k) (B : Matrix (D × D) (D × D) ℂ)
    (x : (Fin L → D) → ℂ) (σ : Fin L → D) :
    (bondOp j k B *ᵥ x) σ =
      ∑ p : D × D, B (σ j, σ k) p * x (Function.update (Function.update σ j p.1) k p.2) := by
  simp only [mulVec, dotProduct, bondOp, of_apply, ite_mul, zero_mul]
  rw [sum_ite_agree_off hjk]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [Function.update_self, Function.update_of_ne hjk]

theorem hamiltonian_mulVec_apply (R : RPRing D ι) (hL : 2 ≤ L) (x : (Fin L → D) → ℂ)
    (σ : Fin L → D) :
    (R.hamiltonian L *ᵥ x) σ =
      ∑ j, ∑ p : D × D, R.bondMatrix (σ j, σ (finRotate L j)) p *
          x (Function.update (Function.update σ j p.1) (finRotate L j) p.2) +
        ∑ j, ∑ b, R.oc (σ j) b * x (Function.update σ j b) := by
  rw [RPRing.hamiltonian, add_mulVec, sum_mulVec, sum_mulVec, Pi.add_apply, Finset.sum_apply,
    Finset.sum_apply]
  congr 1
  · exact Finset.sum_congr rfl fun j _ ↦ by
      rw [RPRing.bond, bondOp_mulVec_apply (ne_finRotate hL j)]
  · exact Finset.sum_congr rfl fun j _ ↦ by rw [RPRing.site, siteOp_mulVec_apply]

end Action

variable {d : ℕ} [NeZero d] {L : ℕ} {ι : Type} [Fintype ι]

/-- The ring `R` has the integer tables `M`: `o = M.o / den` and `bond = M.b / den`. -/
structure Represents (R : RPRing (Fin d) ι) (M : IntRing d) : Prop where
  den_pos : 0 < M.den
  oc : ∀ a b, R.oc a b = (M.o a b : ℂ) / M.den
  bond : ∀ a b c e, R.bondMatrix (a, b) (c, e) = (M.b a b c e : ℂ) / M.den

/-! ### Encoding configurations -/

/-- The index `∑ⱼ σⱼ dʲ` of a configuration. -/
def encode (σ : Fin L → Fin d) : ℕ := (finFunctionFinEquiv σ : ℕ)

theorem encode_eq_sum (σ : Fin L → Fin d) : encode σ = ∑ i, (σ i : ℕ) * d ^ (i : ℕ) :=
  finFunctionFinEquiv_apply σ

@[simp] theorem digitF_encode (σ : Fin L → Fin d) (j : Fin L) : digitF (encode σ) j = σ j := by
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv σ) j
  rw [Equiv.symm_apply_apply] at h
  apply Fin.ext
  rw [digitF, Fin.val_ofNat]
  exact h.symm

@[simp] theorem digitF_encode_succ (σ : Fin L → Fin d) (j : Fin L) :
    digitF (encode σ) (((j : ℕ) + 1) % L) = σ (finRotate L j) := by
  rw [← val_finRotate_eq_mod, digitF_encode]

theorem encode_le (σ : Fin L → Fin d) (j : Fin L) : (σ j : ℕ) * d ^ (j : ℕ) ≤ encode σ := by
  rw [encode_eq_sum]
  exact Finset.single_le_sum (f := fun i ↦ (σ i : ℕ) * d ^ (i : ℕ)) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ j)

theorem encode_update (σ : Fin L → Fin d) (j : Fin L) (b : Fin d) :
    encode (Function.update σ j b) = setDigit (encode σ) j b := by
  have hrest : ∑ i ∈ Finset.univ.erase j, ((Function.update σ j b i : Fin d) : ℕ) * d ^ (i : ℕ) =
      ∑ i ∈ Finset.univ.erase j, (σ i : ℕ) * d ^ (i : ℕ) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have h : encode (Function.update σ j b) + (σ j : ℕ) * d ^ (j : ℕ) =
      encode σ + (b : ℕ) * d ^ (j : ℕ) := by
    rw [encode_eq_sum, encode_eq_sum,
      ← Finset.add_sum_erase Finset.univ (fun i ↦ ((Function.update σ j b i : Fin d) : ℕ) *
        d ^ (i : ℕ)) (Finset.mem_univ j),
      ← Finset.add_sum_erase Finset.univ (fun i ↦ (σ i : ℕ) * d ^ (i : ℕ)) (Finset.mem_univ j),
      hrest, Function.update_self]
    ring
  have hle := encode_le σ j
  rw [setDigit, digitF_encode]
  omega

/-- Sums over configurations are sums over indices `s < d^L`. -/
theorem sum_encode {β : Type*} [AddCommMonoid β] (F : ℕ → β) :
    ∑ σ : Fin L → Fin d, F (encode σ) = ∑ s ∈ Finset.range (d ^ L), F s := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Equiv.sum_comp finFunctionFinEquiv (fun s : Fin (d ^ L) ↦ F s)

/-! ### The Hamiltonian -/

/-- The packed integer vector `v` as a vector on configurations. -/
def vec (v : ℕ) (σ : Fin L → Fin d) : ℂ := ((entry v (encode σ) : ℤ) : ℂ)

variable {R : RPRing (Fin d) ι} {M : IntRing d}

/-- `den (H x)(σ) = M.applyH L v (encode σ)` for `x = vec v`. -/
theorem applyH_encode (h : Represents R M) (hL : 2 ≤ L) (v : ℕ) (σ : Fin L → Fin d) :
    ((M.applyH L v (encode σ) : ℤ) : ℂ) = M.den * ((R.hamiltonian L *ᵥ vec v) σ) := by
  have hden : (M.den : ℂ) ≠ 0 := by exact_mod_cast h.den_pos.ne'
  rw [hamiltonian_mulVec_apply R hL, IntRing.applyH, mul_add, Finset.mul_sum, Finset.mul_sum]
  push_cast
  congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    dsimp only
    rw [term_eq, digitF_encode, digitF_encode_succ, ← val_finRotate_eq_mod, ← encode_update,
      ← encode_update, h.bond, vec]
    push_cast
    field_simp
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [term_eq, digitF_encode, ← encode_update, h.oc, vec]
    push_cast
    field_simp

/-! ### The checker's sums -/

theorem dot_eq (v : ℕ) : ((dot d L v : ℤ) : ℝ) = nsq (vec (d := d) (L := L) v) := by
  change _ = nsq fun σ : Fin L → Fin d ↦ ((entry v (encode σ) : ℤ) : ℂ)
  rw [nsq_intCast, dot, foldl_add_eq_sum, zero_add, ← sum_encode]

theorem residualSq_eq (h : Represents R M) (S : ℤ) (hS : S ≠ 0) (hL : 2 ≤ L) (v : ℕ)
    (lam : ℤ) :
    ((M.residualSq S L v lam : ℤ) : ℝ) = ((M.den : ℝ) * S) ^ 2 * nsq
      (R.hamiltonian L *ᵥ vec v - ((lam / (M.den * S) : ℝ) : ℂ) • vec v) := by
  rw [IntRing.residualSq, foldl_add_eq_sum, zero_add, ← sum_encode, nsq_eq_sum, Finset.mul_sum,
    Int.cast_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Int.cast_pow]
  set t : ℤ := S * M.applyH L v (encode σ) - lam * entry v (encode σ)
  have key : (t : ℂ) = ((M.den * S : ℝ) : ℂ) *
      ((R.hamiltonian L *ᵥ vec v -
        ((lam / (M.den * S) : ℝ) : ℂ) • vec v : (Fin L → Fin d) → ℂ) σ) := by
    simp only [t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [applyH_encode h hL]
    simp only [vec]
    have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS
    have hden : (M.den : ℂ) ≠ 0 := by exact_mod_cast h.den_pos.ne'
    field_simp
  have h1 : ((t : ℤ) : ℝ) ^ 2 = ‖(t : ℂ)‖ ^ 2 := by
    rw [Complex.norm_intCast, sq_abs]
  rw [h1, key, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A residual check gives an eigenvalue within `1 / q` of `lam / (den S)`. -/
theorem exists_near_of_check (h : Represents R M) (S : ℤ) (hS : 0 < S) (hL : 2 ≤ L) (v : ℕ)
    (lam : ℤ) (q : ℕ) (hq : 0 < q) (hdot : 0 < dot d L v)
    (hres : M.residualSq S L v lam * (q : ℤ) ^ 2 ≤ M.den ^ 2 * S ^ 2 * dot d L v) :
    ∃ i, |R.spectrum L i - lam / (M.den * S)| ≤ 1 / q := by
  have : Nonempty (Fin L → Fin d) := ⟨fun _ ↦ 0⟩
  obtain ⟨i, hi⟩ := exists_eigenvalue_near (R.hamiltonian_isHermitian L)
    (vec v) (lam / (M.den * S) : ℝ)
  replace hi : (R.spectrum L i - lam / (M.den * S)) ^ 2 * nsq (vec (d := d) (L := L) v) ≤
      nsq (R.hamiltonian L *ᵥ vec v - ((lam / (M.den * S) : ℝ) : ℂ) • vec v) := hi
  refine ⟨i, ?_⟩
  rw [← dot_eq] at hi
  have hres' : ((M.residualSq S L v lam : ℤ) : ℝ) * (q : ℝ) ^ 2 ≤
      (M.den : ℝ) ^ 2 * (S : ℝ) ^ 2 * ((dot d L v : ℤ) : ℝ) := by exact_mod_cast hres
  rw [residualSq_eq h S hS.ne' hL] at hres'
  have hN : (0 : ℝ) < ((dot d L v : ℤ) : ℝ) := by exact_mod_cast hdot
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hdr : (0 : ℝ) < M.den := by exact_mod_cast h.den_pos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  set e := R.spectrum L i - lam / (M.den * S)
  set N := ((dot d L v : ℤ) : ℝ)
  set r := nsq (R.hamiltonian L *ᵥ vec v - ((lam / (M.den * S) : ℝ) : ℂ) • vec v)
  have h1 : r * (q : ℝ) ^ 2 ≤ N := by
    have h4 : (M.den : ℝ) ^ 2 * (S : ℝ) ^ 2 * (r * (q : ℝ) ^ 2) ≤
        (M.den : ℝ) ^ 2 * (S : ℝ) ^ 2 * N := by
      have e' : ((M.den : ℝ) * S) ^ 2 * r * (q : ℝ) ^ 2 =
          (M.den : ℝ) ^ 2 * (S : ℝ) ^ 2 * (r * (q : ℝ) ^ 2) := by ring
      linarith
    exact le_of_mul_le_mul_left h4 (by positivity)
  have h2 : (e * q) ^ 2 ≤ 1 := by
    have h3 : e ^ 2 * N * (q : ℝ) ^ 2 ≤ N :=
      le_trans (mul_le_mul_of_nonneg_right hi (sq_nonneg _)) h1
    have h5 : N * (e * q) ^ 2 ≤ N * 1 := by
      have e' : N * (e * q) ^ 2 = e ^ 2 * N * (q : ℝ) ^ 2 := by ring
      linarith
    exact le_of_mul_le_mul_left h5 hN
  have h6 : |e * q| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 h2
  rw [abs_mul, abs_of_pos hqr] at h6
  rwa [le_div_iff₀ hqr]

/-! ### Counting -/

theorem intDiv_eq (z w : ℤ) : (z : ℂ) / (w : ℂ) = (((z : ℝ) / (w : ℝ) : ℝ) : ℂ) := by
  push_cast; rfl

theorem gSite_eq (h : Represents R M) (a : Fin d) :
    gSite R.oc a = (M.gSiteZ a : ℝ) / M.den := by
  have hdr : (0 : ℝ) < M.den := by exact_mod_cast h.den_pos
  have h1 : ∀ b, offNorm R.oc a b = ((if a = b then 0 else |M.o a b| : ℤ) : ℝ) / M.den := by
    intro b
    by_cases hab : a = b
    · simp [offNorm, hab]
    · rw [offNorm_of_ne _ hab, h.oc, intDiv_eq, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos hdr]
      simp [hab]
  unfold gSite IntRing.gSiteZ
  rw [h.oc, intDiv_eq, Complex.ofReal_re]
  simp only [h1]
  rw [← Finset.sum_div]
  push_cast
  ring

theorem gBond_eq (h : Represents R M) (a b : Fin d) :
    gBond R.bondMatrix (a, b) = (M.gBondZ a b : ℝ) / M.den := by
  have hdr : (0 : ℝ) < M.den := by exact_mod_cast h.den_pos
  have h1 : ∀ c e, offNorm R.bondMatrix (a, b) (c, e) =
      ((if a = c ∧ b = e then 0 else |M.b a b c e| : ℤ) : ℝ) / M.den := by
    intro c e
    by_cases hp : (a, b) = (c, e)
    · have hp' : a = c ∧ b = e := Prod.mk.injEq a b c e ▸ hp
      simp [offNorm, hp']
    · have hp' : ¬ (a = c ∧ b = e) := fun hh ↦ hp (by rw [hh.1, hh.2])
      rw [offNorm_of_ne _ hp, h.bond, intDiv_eq, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos hdr]
      simp [hp']
  unfold gBond IntRing.gBondZ
  rw [h.bond, intDiv_eq, Complex.ofReal_re, Fintype.sum_prod_type]
  simp only [h1]
  simp only [← Finset.sum_div]
  push_cast
  ring

theorem gersh_eq (h : Represents R M) (σ : Fin L → Fin d) :
    gersh R σ = (M.gershC L (encode σ) : ℝ) / M.den := by
  unfold gersh IntRing.gershC
  simp only [gBond_eq h, gSite_eq h, digitF_encode, digitF_encode_succ, ← Finset.sum_div]
  push_cast
  ring

/-- **Counting.** At most `M.classicalCount L cut` eigenvalues of the ring lie below
`cut / den`. -/
theorem card_low_le (h : Represents R M) (hL : 2 ≤ L) (cut : ℤ) :
    (Finset.univ.filter fun i ↦ R.spectrum L i < (cut : ℝ) / M.den).card ≤
      M.classicalCount L cut := by
  classical
  have hdr : (0 : ℝ) < M.den := by exact_mod_cast h.den_pos
  set B := Finset.univ.filter fun σ : Fin L → Fin d ↦ M.gershC L (encode σ) < cut
  have hB : M.classicalCount L cut = B.card := by
    rw [IntRing.classicalCount, foldl_add_eq_sum, zero_add, ← sum_encode, Finset.card_filter]
  rw [hB]
  refine eigCount_le_card_of_vanishing (R.hamiltonian_isHermitian L) B fun x hx ↦ ?_
  refine le_trans ?_ (qform_hamiltonian_ge R hL x)
  rw [nsq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ ↦ ?_
  by_cases hσ : σ ∈ B
  · simp [hx σ hσ]
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hd : ¬ (M.gershC L (encode σ) < cut) := by simpa [B] using hσ
    have hc : (cut : ℝ) ≤ M.gershC L (encode σ) := by exact_mod_cast not_lt.1 hd
    rw [gersh_eq h]
    exact div_le_div_of_nonneg_right hc hdr.le

end GaugeGaps.KernelSeed
