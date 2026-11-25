import GaugeGaps.KernelSeed.Seed
import GaugeGaps.KernelSeed.TailChecker
import CertifiedGaps.Spectral.TraceBounds

/-!
# The classical tail: a sharper upper bound on the partition function

The Gershgorin form bound dominates the eigenvalue counting function of a ring Hamiltonian by that
of its local Gershgorin function at every threshold (`eigCount_le_gersh`). With the ground energy
located and exactly one configuration below the cut, this gives

`Z_L(β) ≤ e^{-β a₀} + ∑_{σ above the cut} e^{-β g(σ)}`   (`partition_upper_fine`),

and the classical sum is bounded by the integer `tailWeight` over `2^K` (`tail_le`). This replaces
the crude bound, which put all `d^L - 1` excited levels at the cut.
-/

open Real CertifiedGaps CertifiedGaps.Spectral

set_option linter.unusedSectionVars false

namespace GaugeGaps.KernelSeed

variable {d : ℕ} [NeZero d] {L : ℕ} {ι : Type} [Fintype ι] {R : RPRing (Fin d) ι}
  {M : IntRing d}

/-- **Counting domination.** At every threshold the ring has at most as many eigenvalues below it
as there are configurations with Gershgorin value below it. -/
theorem eigCount_le_gersh (R : RPRing (Fin d) ι) (hL : 2 ≤ L) (t : ℝ) :
    eigCount (R.hamiltonian_isHermitian L) t ≤ countBelow Finset.univ (gersh R (L := L)) t := by
  classical
  refine eigCount_le_card_of_vanishing (R.hamiltonian_isHermitian L)
    (Finset.univ.filter fun σ ↦ gersh R σ < t) fun x hx ↦ ?_
  refine le_trans ?_ (qform_hamiltonian_ge R hL x)
  rw [nsq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ ↦ ?_
  by_cases hσ : gersh R σ < t
  · simp [hx σ (by simp [hσ])]
  · exact mul_le_mul_of_nonneg_right (not_lt.1 hσ) (sq_nonneg _)

/-- **The partition function from the located ground energy and the classical tail.** -/
theorem partition_upper_fine {a₀ b₀ ρ β : ℝ} (hβ : 0 ≤ β) (hL : 2 ≤ L) (hb : b₀ < ρ)
    (h : LowSpectrum (R.spectrum L) a₀ b₀ ρ)
    (hone : (Finset.univ.filter fun σ : Fin L → Fin d ↦ gersh R σ < ρ).card ≤ 1) :
    R.partitionFunction L β ≤ exp (-(β * a₀)) +
      ∑ σ : Fin L → Fin d, if gersh R σ < ρ then 0 else exp (-(β * gersh R σ)) := by
  classical
  obtain ⟨i₀, ha, hb₀, hρ⟩ := h
  set f : ℝ → ℝ := fun x ↦ exp (-(β * max x ρ)) with hf
  have hanti : Antitone f := fun x y hxy ↦ exp_le_exp.2 (by
    have := max_le_max_right ρ hxy
    nlinarith)
  have hpos : ∀ x, 0 ≤ f x := fun x ↦ (exp_pos _).le
  have hcmp : ∑ i, f (R.spectrum L i) ≤ ∑ σ : Fin L → Fin d, f (gersh R σ) :=
    sum_le_of_eigCount_le (R.hamiltonian_isHermitian L) hanti hpos Finset.univ
      (gersh R (L := L)) (eigCount_le_gersh R hL)
  have h1 : ∑ i, exp (-(β * R.spectrum L i)) ≤
      exp (-(β * a₀)) + (∑ i, f (R.spectrum L i) - exp (-(β * ρ))) := by
    have e0 : f (R.spectrum L i₀) = exp (-(β * ρ)) := by
      simp only [hf]; rw [max_eq_right (by linarith)]
    have e1 : ∀ i ∈ Finset.univ.erase i₀, f (R.spectrum L i) = exp (-(β * R.spectrum L i)) :=
      fun i hi ↦ by simp only [hf]; rw [max_eq_left (hρ i (Finset.ne_of_mem_erase hi))]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
      ← Finset.add_sum_erase Finset.univ (fun i ↦ f (R.spectrum L i)) (Finset.mem_univ i₀), e0,
      Finset.sum_congr rfl e1]
    have h0 : exp (-(β * R.spectrum L i₀)) ≤ exp (-(β * a₀)) := exp_le_exp.2 (by nlinarith)
    linarith
  have h2 : ∑ σ : Fin L → Fin d, f (gersh R σ) - exp (-(β * ρ)) ≤
      ∑ σ : Fin L → Fin d, if gersh R σ < ρ then 0 else exp (-(β * gersh R σ)) := by
    have e : ∀ σ : Fin L → Fin d, f (gersh R σ) =
        (if gersh R σ < ρ then exp (-(β * ρ)) else 0) +
          (if gersh R σ < ρ then 0 else exp (-(β * gersh R σ))) := by
      intro σ
      by_cases hσ : gersh R σ < ρ
      · simp only [hf, hσ, ↓reduceIte, add_zero]; rw [max_eq_right hσ.le]
      · simp only [hf, hσ, ↓reduceIte, zero_add]; rw [max_eq_left (not_lt.1 hσ)]
    have hc : ∑ σ : Fin L → Fin d, (if gersh R σ < ρ then exp (-(β * ρ)) else 0) ≤
        exp (-(β * ρ)) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.univ.filter fun σ : Fin L → Fin d ↦ gersh R σ < ρ).card : ℝ) ≤ 1 := by
        exact_mod_cast hone
      nlinarith [exp_pos (-(β * ρ))]
    simp only [e, Finset.sum_add_distrib]
    linarith
  rw [RPRing.partitionFunction_eq_sum]
  linarith

/-! ### The tail weight -/

theorem tailWeight_eq_sum (M : IntRing d) (cut mul num0 dv : ℤ) (K : ℕ) :
    M.tailWeight L cut mul num0 dv K =
      ∑ σ : Fin L → Fin d, tailTerm cut mul num0 dv K (M.gershC L (encode σ)) := by
  rw [IntRing.tailWeight, foldl_add_eq_sum, zero_add, ← sum_encode]

/-- A tail weight assembled from chunks checked one declaration at a time. -/
theorem tailWeight_of_chunks (M : IntRing d) (n : ℕ) (cut mul num0 dv : ℤ) (K k m : ℕ)
    (hkm : k * m = d ^ n) (vals : List ℕ)
    (h : ∀ c, c < k → M.tailChunk n cut mul num0 dv K (c * m) m = vals.getD c 0) :
    M.tailWeight n cut mul num0 dv K = ∑ c ∈ Finset.range k, vals.getD c 0 := by
  rw [IntRing.tailWeight, ← hkm, foldl_add_eq_sum, zero_add, sum_blocks]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [← h c (Finset.mem_range.1 hc), IntRing.tailChunk, foldl_add_eq_sum, zero_add]

/-- One configuration above the cut: `e^{-x} ≤ 2^(K - min(k, K)) / 2^K` when `k log 2 ≤ x`. -/
theorem exp_le_tailTerm {mul num0 dv g : ℤ} (K : ℕ) (hdv : 0 < dv) {x : ℝ} (hx : 0 ≤ x)
    (hlin : ((g : ℝ) * mul - num0) / dv * 0.6931471808 ≤ x) :
    exp (-x) ≤ ((2 ^ (K - min (tailExp mul num0 dv g) K) : ℕ) : ℝ) / 2 ^ K := by
  set k := tailExp mul num0 dv g with hk
  set j := min k K with hj
  have hjK : j ≤ K := min_le_right _ _
  have hdvr : (0 : ℝ) < dv := by exact_mod_cast hdv
  have hlog : log 2 ≤ 0.6931471808 := log_two_lt_d9.le
  have hlog0 : 0 ≤ log 2 := log_nonneg (by norm_num)
  -- `k log 2 ≤ x`
  have hkx : (k : ℝ) * log 2 ≤ x := by
    by_cases hz : 0 ≤ (g * mul - num0) / dv
    · have hfl : (((g * mul - num0) / dv : ℤ) : ℝ) ≤ ((g : ℝ) * mul - num0) / dv := by
        rw [le_div_iff₀ hdvr]
        exact_mod_cast Int.ediv_mul_le (g * mul - num0) hdv.ne'
      have hkc : (k : ℝ) = (((g * mul - num0) / dv : ℤ) : ℝ) := by
        rw [hk, tailExp]
        exact_mod_cast Int.toNat_of_nonneg hz
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      calc (k : ℝ) * log 2 ≤ (k : ℝ) * 0.6931471808 := mul_le_mul_of_nonneg_left hlog hk0
        _ ≤ ((g : ℝ) * mul - num0) / dv * 0.6931471808 :=
            mul_le_mul_of_nonneg_right (hkc ▸ hfl) (by norm_num)
        _ ≤ x := hlin
    · have hk0 : k = 0 := by
        rw [hk, tailExp]
        exact Int.toNat_of_nonpos (not_le.1 hz).le
      rw [hk0]; simpa using hx
  have hjx : (j : ℝ) * log 2 ≤ x := by
    have hjk : (j : ℝ) ≤ k := by exact_mod_cast min_le_left k K
    nlinarith
  have h2 : (((2 ^ (K - j) : ℕ) : ℝ)) / 2 ^ K = ((2 : ℝ) ^ j)⁻¹ := by
    push_cast
    rw [pow_sub₀ (2 : ℝ) (by norm_num) hjK]
    field_simp
  rw [h2]
  calc exp (-x) ≤ exp (-((j : ℝ) * log 2)) := exp_le_exp.2 (by linarith)
    _ = ((2 : ℝ) ^ j)⁻¹ := by
        rw [exp_neg, exp_nat_mul, exp_log (by norm_num)]

/-- **The classical tail is at most `tailWeight / 2^K`.** -/
theorem tail_le (h : Represents R M) (cut mul num0 dv : ℤ) (K : ℕ) (hdv : 0 < dv)
    {β a₀ : ℝ} (hβ : 0 ≤ β) (h1 : (mul : ℝ) / dv * 0.6931471808 = β / M.den)
    (h2 : β * a₀ ≤ (num0 : ℝ) / dv * 0.6931471808) (hcut : a₀ ≤ (cut : ℝ) / M.den) :
    ∑ σ : Fin L → Fin d,
        (if gersh R σ < (cut : ℝ) / M.den then 0 else exp (-(β * gersh R σ))) ≤
      exp (-(β * a₀)) * ((M.tailWeight L cut mul num0 dv K : ℝ) / 2 ^ K) := by
  have hdr : (0 : ℝ) < M.den := by exact_mod_cast h.den_pos
  rw [tailWeight_eq_sum, Nat.cast_sum, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ ↦ ?_
  rw [gersh_eq h]
  set g := M.gershC L (encode σ) with hg
  by_cases hlt : g < cut
  · have hlt' : (g : ℝ) / M.den < (cut : ℝ) / M.den :=
      div_lt_div_of_pos_right (by exact_mod_cast hlt) hdr
    rw [ite_eq_left hlt']
    positivity
  · have hge : (cut : ℝ) / M.den ≤ (g : ℝ) / M.den :=
      div_le_div_of_nonneg_right (by exact_mod_cast not_lt.1 hlt) hdr.le
    rw [ite_eq_right (not_lt.2 hge), tailTerm, ite_eq_right hlt]
    have hx : 0 ≤ β * ((g : ℝ) / M.den - a₀) := mul_nonneg hβ (by linarith)
    have hlin : ((g : ℝ) * mul - num0) / dv * 0.6931471808 ≤ β * ((g : ℝ) / M.den - a₀) := by
      have e : ((g : ℝ) * mul - num0) / dv * 0.6931471808 =
          (g : ℝ) * ((mul : ℝ) / dv * 0.6931471808) - (num0 : ℝ) / dv * 0.6931471808 := by ring
      rw [e, h1]
      have e2 : β * ((g : ℝ) / M.den - a₀) = (g : ℝ) * (β / M.den) - β * a₀ := by ring
      rw [e2]
      linarith
    have key := exp_le_tailTerm (mul := mul) (num0 := num0) (g := g) K hdv hx hlin
    calc exp (-(β * ((g : ℝ) / M.den)))
        = exp (-(β * a₀)) * exp (-(β * ((g : ℝ) / M.den - a₀))) := by
          rw [← exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key (exp_pos _).le

/-- The number of configurations with Gershgorin value below `cut / den` is the classical count. -/
theorem card_gersh_lt (h : Represents R M) (cut : ℤ) :
    (Finset.univ.filter fun σ : Fin L → Fin d ↦ gersh R σ < (cut : ℝ) / M.den).card =
      M.classicalCount L cut := by
  classical
  have hdr : (0 : ℝ) < M.den := by exact_mod_cast h.den_pos
  rw [IntRing.classicalCount, foldl_add_eq_sum, zero_add, ← sum_encode, Finset.card_filter]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [gersh_eq h]
  have hiff : ((M.gershC L (encode σ) : ℝ) / M.den < (cut : ℝ) / M.den) ↔
      M.gershC L (encode σ) < cut := by
    rw [div_lt_div_iff_of_pos_right hdr]
    exact_mod_cast Iff.rfl
  simp only [hiff]

/-- **The partition function of a ring**, from the low spectrum, the classical count and the tail
weight: `Z ≤ e^{-β a₀} (1 + W / 2^K)`. -/
theorem partition_upper_tail (h : Represents R M) (hL : 2 ≤ L) {a₀ b₀ β : ℝ} (hβ : 0 ≤ β)
    (cut : ℤ) (hlow : LowSpectrum (R.spectrum L) a₀ b₀ ((cut : ℝ) / M.den))
    (hb : b₀ < (cut : ℝ) / M.den) (hcount : M.classicalCount L cut = 1) (mul num0 dv : ℤ)
    (K : ℕ) (hdv : 0 < dv) (h1 : (mul : ℝ) / dv * 0.6931471808 = β / M.den)
    (h2 : β * a₀ ≤ (num0 : ℝ) / dv * 0.6931471808) :
    R.partitionFunction L β ≤
      exp (-(β * a₀)) * (1 + (M.tailWeight L cut mul num0 dv K : ℝ) / 2 ^ K) := by
  have hcut : a₀ ≤ (cut : ℝ) / M.den := by
    obtain ⟨i₀, ha, hb₀, -⟩ := hlow
    linarith
  have hone : (Finset.univ.filter fun σ : Fin L → Fin d ↦
      gersh R σ < (cut : ℝ) / M.den).card ≤ 1 := by rw [card_gersh_lt h, hcount]
  have hfine := partition_upper_fine hβ hL hb hlow hone
  have htail := tail_le (L := L) h cut mul num0 dv K hdv hβ h1 h2 hcut
  rw [mul_add, mul_one]
  linarith

/-- **The spatial seed** from an upper bound on `Z_n` and a lower bound on `Z_{2n}`. -/
theorem seed_spatial_of_tail {n : ℕ} {a₂ b₄ β s tb : ℝ}
    (hu : R.partitionFunction n β ≤ exp (-(β * a₂)) * (1 + tb)) (htb : 0 ≤ tb)
    (hl : exp (-(β * b₄)) ≤ R.partitionFunction (2 * n) β)
    (hs : 1 - s ≤ (1 - β * (b₄ - 2 * a₂)) / (1 + tb) ^ 2) : 1 - s ≤ R.spatialPurity n β := by
  have : Nonempty (Fin d) := ⟨0⟩
  have hfinal := ratio_ge (Z₁ := R.partitionFunction n β) (Z₂ := R.partitionFunction (2 * n) β)
    (x := β * (b₄ - 2 * a₂)) (exp_pos (-(β * a₂))) (R.partitionFunction_pos n β) hu ?_ htb
    le_rfl
  · exact hs.trans hfinal
  · refine le_trans (le_of_eq ?_) hl
    rw [← exp_nat_mul, ← exp_add]
    congr 1; push_cast; ring

/-- **The thermal seed** from an upper bound on `Z_N(β)` and a lower bound on `Z_N(2β)`. -/
theorem seed_thermal_of_tail {N : ℕ} {a b β t tb : ℝ}
    (hu : R.partitionFunction N β ≤ exp (-(β * a)) * (1 + tb)) (htb : 0 ≤ tb)
    (hl : exp (-(2 * β * b)) ≤ R.partitionFunction N (2 * β))
    (ht : 1 - t ≤ (1 - 2 * β * (b - a)) / (1 + tb) ^ 2) : 1 - t ≤ R.thermalPurity N β := by
  have : Nonempty (Fin d) := ⟨0⟩
  have hfinal := ratio_ge (Z₁ := R.partitionFunction N β) (Z₂ := R.partitionFunction N (2 * β))
    (x := 2 * β * (b - a)) (exp_pos (-(β * a))) (R.partitionFunction_pos N β) hu ?_ htb le_rfl
  · exact ht.trans hfinal
  · refine le_trans (le_of_eq ?_) hl
    rw [← exp_nat_mul, ← exp_add]
    congr 1; push_cast; ring

end GaugeGaps.KernelSeed
