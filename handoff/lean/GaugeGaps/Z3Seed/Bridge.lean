import GaugeGaps.Z3Seed.Hamiltonian
import GaugeGaps.Z3Seed.Checker

/-!
# From the integer checker to the ring Hamiltonian

`encode σ = ∑ⱼ σⱼ 3ʲ` identifies configurations with indices. Shifting a link is `shiftN` on
indices (`encode_shiftAt`), `2 (H x)(σ)` is `applyH` at `encode σ` for `x = vec v`
(`applyH_encode`), and the folds of the checker are the squared norms of `vec v` and of
`H x - θ x` (`dot_eq`, `residualSq_eq`). `exists_near_of_check` turns a residual check into an
eigenvalue near `θ`. The structure follows `SeedKernel/Ising/Bridge.lean` of CertifiedGaps.
-/

open Matrix Complex CertifiedGaps CertifiedGaps.Spectral

namespace GaugeGaps.Z3Seed

open GaugeGaps.Z3GaugeHiggs

variable {L : ℕ}

theorem foldl_add_eq_sum {β : Type*} [AddCommMonoid β] (f : ℕ → β) (b : β) (N : ℕ) :
    (List.range N).foldl (fun a s ↦ a + f s) b = b + ∑ s ∈ Finset.range N, f s := by
  induction N generalizing b with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp [add_assoc]

/-! ### Encoding configurations -/

/-- The index `∑ⱼ σⱼ 3ʲ` of a configuration. -/
def encode (σ : Fin L → Fin 3) : ℕ := (finFunctionFinEquiv σ : ℕ)

theorem encode_eq_sum (σ : Fin L → Fin 3) : encode σ = ∑ i, (σ i : ℕ) * 3 ^ (i : ℕ) :=
  finFunctionFinEquiv_apply σ

theorem digit_encode (σ : Fin L → Fin 3) (j : Fin L) : digit (encode σ) j = σ j := by
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv σ) j
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

theorem encode_le (σ : Fin L → Fin 3) (j : Fin L) : (σ j : ℕ) * 3 ^ (j : ℕ) ≤ encode σ := by
  rw [encode_eq_sum]
  exact Finset.single_le_sum (f := fun i ↦ (σ i : ℕ) * 3 ^ (i : ℕ)) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ j)

theorem encode_update (σ : Fin L → Fin 3) (j : Fin L) (b : Fin 3) :
    encode (Function.update σ j b) + (σ j : ℕ) * 3 ^ (j : ℕ) =
      encode σ + (b : ℕ) * 3 ^ (j : ℕ) := by
  have hrest : ∑ i ∈ Finset.univ.erase j, ((Function.update σ j b i : Fin 3) : ℕ) * 3 ^ (i : ℕ) =
      ∑ i ∈ Finset.univ.erase j, (σ i : ℕ) * 3 ^ (i : ℕ) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [encode_eq_sum, encode_eq_sum,
    ← Finset.add_sum_erase Finset.univ (fun i ↦ ((Function.update σ j b i : Fin 3) : ℕ) *
      3 ^ (i : ℕ)) (Finset.mem_univ j),
    ← Finset.add_sum_erase Finset.univ (fun i ↦ (σ i : ℕ) * 3 ^ (i : ℕ)) (Finset.mem_univ j),
    hrest, Function.update_self]
  ring

/-- Shifting the link `j` is `shiftN` on indices. -/
theorem encode_shiftAt (j : Fin L) (a : Fin 3) (σ : Fin L → Fin 3) :
    encode (shiftAt j a σ) = shiftN (encode σ) j a := by
  have h := encode_update σ j (σ j + a)
  have hle := encode_le σ j
  have hv : ((σ j + a : Fin 3) : ℕ) = ((σ j : ℕ) + (a : ℕ)) % 3 := Fin.val_add _ _
  rw [shiftN, digit_encode, shiftAt, ← hv]
  omega

/-- Sums over configurations are sums over indices `s < 3^L`. -/
theorem sum_encode {β : Type*} [AddCommMonoid β] (F : ℕ → β) :
    ∑ σ : Fin L → Fin 3, F (encode σ) = ∑ s ∈ Finset.range (3 ^ L), F s := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Equiv.sum_comp finFunctionFinEquiv (fun s : Fin (3 ^ L) ↦ F s)

/-! ### The Hamiltonian -/

/-- The integer vector `v` as a vector on configurations. -/
def vec (v : List ℤ) (σ : Fin L → Fin 3) : ℂ := ((entry v (encode σ) : ℤ) : ℂ)

theorem diagSum_encode (σ : Fin L → Fin 3) :
    ((diagSum L (encode σ) : ℤ) : ℝ) = ∑ j, dR (σ j) := by
  rw [diagSum, foldl_add_eq_sum, zero_add,
    ← Fin.sum_univ_eq_sum_range (fun j ↦ dZ (digit (encode σ) j))]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [digit_encode]
  generalize σ j = a
  fin_cases a <;> simp [dZ, dR]

/-- `2 (H x)(σ) = applyH e κ L v (encode σ)` for `x = vec v`. -/
theorem applyH_encode (eZ κZ : ℤ) (hL : 2 ≤ L) (v : List ℤ) (σ : Fin L → Fin 3) :
    ((applyH eZ κZ L v (encode σ) : ℤ) : ℂ) =
      2 * ((model eZ κZ).hamiltonian L *ᵥ vec v) σ := by
  have h1 (j : Fin L) (a : Fin 3) :
      vec v (shiftAt j a σ) = ((entry v (shiftN (encode σ) j a) : ℤ) : ℂ) := by
    rw [vec, encode_shiftAt]
  have h2 (j : Fin L) (a b : Fin 3) : vec v (shiftAt (finRotate L j) b (shiftAt j a σ)) =
      ((entry v (shiftN (shiftN (encode σ) j a) ((j + 1) % L) b) : ℤ) : ℂ) := by
    rw [vec, encode_shiftAt, encode_shiftAt, val_finRotate_eq_mod]
  have hd : (diagE (κZ : ℝ) σ : ℂ) = -((κZ : ℂ) / 2) * ((diagSum L (encode σ) : ℤ) : ℂ) := by
    have h := diagSum_encode σ
    rw [diagE, ← h]
    push_cast
    ring
  rw [hamiltonian_mulVec_apply _ _ hL, applyH, foldl_add_eq_sum, foldl_add_eq_sum, zero_add,
    zero_add,
    ← Fin.sum_univ_eq_sum_range
      (fun j ↦ entry v (shiftN (encode σ) j 1) + entry v (shiftN (encode σ) j 2)),
    ← Fin.sum_univ_eq_sum_range
      (fun j ↦ entry v (shiftN (shiftN (encode σ) j 1) ((j + 1) % L) 2) +
        entry v (shiftN (shiftN (encode σ) j 2) ((j + 1) % L) 1))]
  simp only [h1, h2, hd]
  rw [vec]
  push_cast
  simp only [Fin.val_one, Fin.val_two]
  ring

/-! ### The checker's sums -/

theorem dot_eq (v : List ℤ) : ((dot L v : ℤ) : ℝ) = nsq (vec (L := L) v) := by
  change _ = nsq fun σ : Fin L → Fin 3 ↦ ((entry v (encode σ) : ℤ) : ℂ)
  rw [nsq_intCast, dot, foldl_add_eq_sum, zero_add, ← sum_encode]

theorem residualSq_eq (eZ κZ S : ℤ) (hS : S ≠ 0) (hL : 2 ≤ L) (v : List ℤ) (lam : ℤ) :
    ((residualSq eZ κZ S L v lam : ℤ) : ℝ) = (2 * (S : ℝ)) ^ 2 * nsq
      ((model eZ κZ).hamiltonian L *ᵥ vec v - ((lam / (2 * S) : ℝ) : ℂ) • vec v) := by
  rw [residualSq, foldl_add_eq_sum, zero_add, ← sum_encode, nsq_eq_sum, Finset.mul_sum,
    Int.cast_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Int.cast_pow]
  set t : ℤ := S * applyH eZ κZ L v (encode σ) - lam * entry v (encode σ)
  have key : (t : ℂ) = ((2 * S : ℝ) : ℂ) *
      (((model eZ κZ).hamiltonian L *ᵥ vec v -
        ((lam / (2 * S) : ℝ) : ℂ) • vec v : (Fin L → Fin 3) → ℂ) σ) := by
    simp only [t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [applyH_encode eZ κZ hL]
    simp only [vec]
    have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS
    field_simp
  have h1 : ((t : ℤ) : ℝ) ^ 2 = ‖(t : ℂ)‖ ^ 2 := by
    rw [Complex.norm_intCast, sq_abs]
  rw [h1, key, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A residual check gives an eigenvalue within `1 / q` of `lam / (2 S)`. -/
theorem exists_near_of_check (eZ κZ S : ℤ) (hS : 0 < S) (hL : 2 ≤ L) (v : List ℤ) (lam : ℤ)
    (q : ℕ) (hq : 0 < q) (hdot : 0 < dot L v)
    (hres : residualSq eZ κZ S L v lam * (q : ℤ) ^ 2 ≤ 4 * S ^ 2 * dot L v) :
    ∃ i, |(model eZ κZ).spectrum L i - lam / (2 * S)| ≤ 1 / q := by
  have : Nonempty (Fin L → Fin 3) := ⟨fun _ ↦ 0⟩
  obtain ⟨i, hi⟩ := exists_eigenvalue_near ((model eZ κZ).hamiltonian_isHermitian L)
    (vec v) (lam / (2 * S) : ℝ)
  replace hi : ((model eZ κZ).spectrum L i - lam / (2 * S)) ^ 2 * nsq (vec (L := L) v) ≤
      nsq ((model eZ κZ).hamiltonian L *ᵥ vec v - ((lam / (2 * S) : ℝ) : ℂ) • vec v) := hi
  refine ⟨i, ?_⟩
  rw [← dot_eq] at hi
  have hres' : ((residualSq eZ κZ S L v lam : ℤ) : ℝ) * (q : ℝ) ^ 2 ≤
      4 * (S : ℝ) ^ 2 * ((dot L v : ℤ) : ℝ) := by exact_mod_cast hres
  rw [residualSq_eq eZ κZ S hS.ne' hL] at hres'
  have hN : (0 : ℝ) < ((dot L v : ℤ) : ℝ) := by exact_mod_cast hdot
  set d := (model eZ κZ).spectrum L i - lam / (2 * S)
  set N := ((dot L v : ℤ) : ℝ)
  set r := nsq ((model eZ κZ).hamiltonian L *ᵥ vec v - ((lam / (2 * S) : ℝ) : ℂ) • vec v)
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : r * (q : ℝ) ^ 2 ≤ N := by
    have h4 : 4 * (S : ℝ) ^ 2 * (r * (q : ℝ) ^ 2) ≤ 4 * (S : ℝ) ^ 2 * N := by
      have e : (2 * (S : ℝ)) ^ 2 * r * (q : ℝ) ^ 2 = 4 * (S : ℝ) ^ 2 * (r * (q : ℝ) ^ 2) := by
        ring
      linarith
    exact le_of_mul_le_mul_left h4 (by positivity)
  have h2 : (d * q) ^ 2 ≤ 1 := by
    have h3 : d ^ 2 * N * (q : ℝ) ^ 2 ≤ N :=
      le_trans (mul_le_mul_of_nonneg_right hi (sq_nonneg _)) h1
    have h5 : N * (d * q) ^ 2 ≤ N * 1 := by
      have e : N * (d * q) ^ 2 = d ^ 2 * N * (q : ℝ) ^ 2 := by ring
      linarith
    exact le_of_mul_le_mul_left h5 hN
  have h6 : |d * q| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 h2
  rw [abs_mul, abs_of_pos hqr] at h6
  rwa [le_div_iff₀ hqr]

end GaugeGaps.Z3Seed
