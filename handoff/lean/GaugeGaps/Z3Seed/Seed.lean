import GaugeGaps.Z3Seed.Bridge
import GaugeGaps.Z3Seed.Data
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A spectral gap for the `ℤ₃` gauge–Higgs chain with no hypothesis

At `e = 1`, `κ = 16` (deep in the Higgs regime; the matter kinetic coefficient is the unit of
energy) the seed purities of `Z3GaugeHiggs.model` on rings of 2 and 4 links are proved here from
kernel computations:

* a residual check of an integer trial vector on each ring pins the ground energy to within
  `10⁻⁶` (`exists_near_of_check`);
* the comparison with the classical energies puts every other eigenvalue above
  `ρ_L = -16 L + 24 - 2 L` (`card_low_le`);
* the resulting bounds on the partition functions give the seed purities at `β₀ = 14/25`.

`gap` is then the theorem `RPRing.gapGT_of_chainCertificate` of the CertifiedGaps library with
every hypothesis discharged. The proof follows `SeedKernel/Ising/Seed.lean` of that library, with
one located eigenvalue instead of two.
-/

open Real CertifiedGaps

namespace GaugeGaps.Z3Seed

open GaugeGaps.Z3GaugeHiggs

variable {L : ℕ}

/-! ### Partition functions from a located ground energy -/

/-- One eigenvalue in `[a₀, b₀]` and all others at least `ρ`. -/
def LowSpectrum {ι : Type*} (E : ι → ℝ) (a₀ b₀ ρ : ℝ) : Prop :=
  ∃ i₀, a₀ ≤ E i₀ ∧ E i₀ ≤ b₀ ∧ ∀ i, i ≠ i₀ → ρ ≤ E i

theorem sum_exp_ge {ι : Type*} [Fintype ι] {E : ι → ℝ} {a₀ b₀ ρ β : ℝ} (hβ : 0 ≤ β)
    (h : LowSpectrum E a₀ b₀ ρ) : exp (-(β * b₀)) ≤ ∑ i, exp (-(β * E i)) := by
  obtain ⟨i₀, -, hb, -⟩ := h
  calc exp (-(β * b₀)) ≤ exp (-(β * E i₀)) := exp_le_exp.2 (by nlinarith)
    _ ≤ ∑ i, exp (-(β * E i)) :=
      Finset.single_le_sum (f := fun i ↦ exp (-(β * E i))) (fun i _ ↦ (exp_pos _).le)
        (Finset.mem_univ i₀)

theorem sum_exp_le {ι : Type*} [Fintype ι] {E : ι → ℝ} {a₀ b₀ ρ β : ℝ} (hβ : 0 ≤ β)
    (h : LowSpectrum E a₀ b₀ ρ) :
    ∑ i, exp (-(β * E i)) ≤ exp (-(β * a₀)) + Fintype.card ι * exp (-(β * ρ)) := by
  classical
  obtain ⟨i₀, ha, -, hρ⟩ := h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  refine add_le_add (exp_le_exp.2 (by nlinarith)) ?_
  calc ∑ i ∈ Finset.univ.erase i₀, exp (-(β * E i))
      ≤ ∑ _i ∈ Finset.univ.erase i₀, exp (-(β * ρ)) :=
        Finset.sum_le_sum fun i hi ↦
          exp_le_exp.2 (by nlinarith [hρ i (Finset.ne_of_mem_erase hi)])
    _ ≤ Fintype.card ι * exp (-(β * ρ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (Finset.card_le_univ _)

/-- **The low spectrum of a ring** from one residual check and the classical count. -/
theorem lowSpectrum_of_check {e κ : ℝ} (eZ κZ S : ℤ) (he : e = eZ) (hκ : κ = κZ)
    (heZ : 0 ≤ eZ) (hκZ : 0 ≤ κZ) (hS : 0 < S) (hL : 2 ≤ L) (v : List ℤ) (lam : ℤ) (q : ℕ)
    (hq : 0 < q) (hdot : 0 < dot L v)
    (hres : residualSq eZ κZ S L v lam * (q : ℤ) ^ 2 ≤ 4 * S ^ 2 * dot L v)
    (hρ : (lam : ℝ) / (2 * S) + 1 / q < -(κ * L) + 3 * κ / 2 - (e + 1) * L) :
    LowSpectrum ((model e κ).spectrum L) (lam / (2 * S) - 1 / q) (lam / (2 * S) + 1 / q)
      (-(κ * L) + 3 * κ / 2 - (e + 1) * L) := by
  classical
  subst he hκ
  obtain ⟨i₀, h₀⟩ := exists_near_of_check eZ κZ S hS hL v lam q hq hdot hres
  have h₀' := abs_le.1 h₀
  refine ⟨i₀, by linarith [h₀'.1], by linarith [h₀'.2], fun i hi ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  have hsub : ({i₀, i} : Finset (Fin L → Fin 3)) ⊆ Finset.univ.filter fun j ↦
      (model (eZ : ℝ) (κZ : ℝ)).spectrum L j <
        -((κZ : ℝ) * L) + 3 * (κZ : ℝ) / 2 - ((eZ : ℝ) + 1) * L := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hj with rfl | rfl
    · linarith [h₀'.2]
    · exact hlt
  have h2 : ({i₀, i} : Finset (Fin L → Fin 3)).card = 2 := Finset.card_pair (Ne.symm hi)
  have h3 := (Finset.card_le_card hsub).trans
    (card_low_le (eZ : ℝ) (κZ : ℝ) (by exact_mod_cast heZ) (by exact_mod_cast hκZ) hL)
  omega

/-- `Z ≤ A (1 + 3^L e^{-β(ρ - a₀)})` with `A = e^{-β a₀}`. -/
theorem partition_upper {e κ a₀ b₀ ρ β : ℝ} (hβ : 0 ≤ β)
    (h : LowSpectrum ((model e κ).spectrum L) a₀ b₀ ρ) :
    (model e κ).partitionFunction L β ≤
      exp (-(β * a₀)) * (1 + 3 ^ L * exp (-(β * (ρ - a₀)))) := by
  classical
  rw [RPRing.partitionFunction_eq_sum]
  refine (sum_exp_le hβ h).trans (le_of_eq ?_)
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, mul_add,
    mul_one, ← exp_add, mul_left_comm (exp (-(β * a₀))) (3 ^ L)]
  ring_nf

theorem partition_lower {e κ a₀ b₀ ρ β : ℝ} (hβ : 0 ≤ β)
    (h : LowSpectrum ((model e κ).spectrum L) a₀ b₀ ρ) :
    exp (-(β * b₀)) ≤ (model e κ).partitionFunction L β := by
  rw [RPRing.partitionFunction_eq_sum]
  exact sum_exp_ge hβ h

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

/-! ### The kernel checks -/

theorem dot2_pos : 0 < dot 2 v2 := by decide +kernel

theorem dot4_pos : 0 < dot 4 v4 := by decide +kernel

theorem res2 : residualSq 1 16 scale 2 v2 lam2 * ((10 ^ 6 : ℕ) : ℤ) ^ 2 ≤
    4 * scale ^ 2 * dot 2 v2 := by decide +kernel

theorem res4 : residualSq 1 16 scale 4 v4 lam4 * ((10 ^ 6 : ℕ) : ℤ) ^ 2 ≤
    4 * scale ^ 2 * dot 4 v4 := by decide +kernel

/-! ### The two rings -/

/-- The eigenvalue radius certified by the residual checks. -/
noncomputable abbrev rad : ℝ := 1 / ((10 ^ 6 : ℕ) : ℝ)

/-- The trial energy on the ring of 2 links. -/
noncomputable abbrev θ2 : ℝ := (lam2 : ℝ) / (2 * (scale : ℝ))

/-- The trial energy on the ring of 4 links. -/
noncomputable abbrev θ4 : ℝ := (lam4 : ℝ) / (2 * (scale : ℝ))

/-- The classical cut `-κL + 3κ/2 - (e + 1)L` at `e = 1`, `κ = 16`. -/
noncomputable abbrev cut (L : ℕ) : ℝ := -(16 * (L : ℝ)) + 3 * 16 / 2 - (1 + 1) * (L : ℝ)

theorem lowSpectrum2 :
    LowSpectrum ((model 1 16).spectrum 2) (θ2 - rad) (θ2 + rad) (cut 2) :=
  lowSpectrum_of_check (e := 1) (κ := 16) 1 16 scale (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) le_rfl v2 lam2 (10 ^ 6) (by norm_num) dot2_pos res2
    (by norm_num [lam2, scale])

theorem lowSpectrum4 :
    LowSpectrum ((model 1 16).spectrum 4) (θ4 - rad) (θ4 + rad) (cut 4) :=
  lowSpectrum_of_check (e := 1) (κ := 16) 1 16 scale (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by norm_num) v4 lam4 (10 ^ 6) (by norm_num) dot4_pos res4
    (by norm_num [lam4, scale])

/-! ### The seeds -/

/-- **The spatial seed**, with no hypothesis. -/
theorem seed_spatial : 1 - (2428e-5 : ℝ) ≤ (model 1 16).spatialPurity 2 (14 / 25) := by
  set β : ℝ := 14 / 25
  have hβ : (0 : ℝ) ≤ β := by norm_num [β]
  have hu := partition_upper hβ lowSpectrum2
  have hl := partition_lower hβ lowSpectrum4
  set T := (3 : ℝ) ^ 2 * exp (-(β * (cut 2 - (θ2 - rad))))
  set Q : ℝ := 1 / 2.7182818283 ^ 11
  have hT : T ≤ 3 ^ 2 * Q := by
    have e1 : exp (-(β * (cut 2 - (θ2 - rad)))) ≤ exp (-((11 : ℕ) : ℝ)) :=
      exp_le_exp.2 (by norm_num [β, θ2, cut, rad, lam2, scale])
    exact mul_le_mul_of_nonneg_left (e1.trans (exp_neg_nat_le 11)) (by norm_num)
  have hT0 : 0 ≤ T := by positivity
  have hfinal := ratio_ge (Z₁ := (model 1 16).partitionFunction 2 β)
    (Z₂ := (model 1 16).partitionFunction 4 β) (exp_pos (-(β * (θ2 - rad))))
    ((model 1 16).partitionFunction_pos 2 β) hu ?_ hT0 hT
    (x := β * ((θ4 + rad) - 2 * (θ2 - rad)))
  · refine le_trans ?_ hfinal
    norm_num [Q, θ2, θ4, β, rad, lam2, lam4, scale]
  · refine le_trans (le_of_eq ?_) hl
    rw [← exp_nat_mul, ← exp_add]
    congr 1; push_cast; ring

/-- **The thermal seed**, with no hypothesis. -/
theorem seed_thermal : 1 - (197e-4 : ℝ) ≤ (model 1 16).thermalPurity 4 (14 / 25) := by
  set β : ℝ := 14 / 25
  have hβ : (0 : ℝ) ≤ β := by norm_num [β]
  have hu := partition_upper hβ lowSpectrum4
  have hl := partition_lower (β := 2 * β) (by positivity) lowSpectrum4
  set T := (3 : ℝ) ^ 4 * exp (-(β * (cut 4 - (θ4 - rad))))
  set Q : ℝ := 1 / 2.7182818283 ^ 9
  have hT : T ≤ 3 ^ 4 * Q := by
    have e1 : exp (-(β * (cut 4 - (θ4 - rad)))) ≤ exp (-((9 : ℕ) : ℝ)) :=
      exp_le_exp.2 (by norm_num [β, θ4, cut, rad, lam4, scale])
    exact mul_le_mul_of_nonneg_left (e1.trans (exp_neg_nat_le 9)) (by norm_num)
  have hT0 : 0 ≤ T := by positivity
  have hfinal := ratio_ge (Z₁ := (model 1 16).partitionFunction 4 β)
    (Z₂ := (model 1 16).partitionFunction 4 (2 * β)) (exp_pos (-(β * (θ4 - rad))))
    ((model 1 16).partitionFunction_pos 4 β) hu ?_ hT0 hT (x := 4 * β * rad)
  · refine le_trans ?_ hfinal
    norm_num [Q, β, rad]
  · refine le_trans (le_of_eq ?_) hl
    rw [← exp_nat_mul, ← exp_add]
    congr 1; push_cast; ring

/-! ### The theorem -/

theorem cert_valid : cert.Valid := by decide +kernel

/-- **A spectral gap with no hypothesis.** The `ℤ₃` gauge–Higgs chain at `e = 1`, `κ = 16`: every
ring of even length `L ≥ 2` has a nondegenerate ground state and a gap above
`log r / β₀ = log 12.62 / (14/25) ≈ 4.527`. -/
theorem gap {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT ((model 1 16).spectrum L) (log (cert.r : ℝ) / (14 / 25)) := by
  have hs : 1 - ((cert.sAt 0 : ℚ) : ℝ) ≤ (model 1 16).spatialPurity 2 (14 / 25) := by
    convert seed_spatial using 2
    norm_num [cert, ChainCertificate.sAt]
  have ht : 1 - ((cert.tAt 0 : ℚ) : ℝ) ≤ (model 1 16).thermalPurity (2 * 2) (14 / 25) := by
    convert seed_thermal using 2
    norm_num [cert, ChainCertificate.tAt]
  exact (model 1 16).gapGT_of_chainCertificate (n₀ := 2) le_rfl (by decide) (by norm_num)
    cert_valid ⟨rfl, rfl, rfl⟩ hs ht hL hLe

/-- The same theorem with the numbers written out. -/
theorem z3_gauge_higgs_gap {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT ((model 1 16).spectrum L) (log (1262 / 100) / (14 / 25)) := by
  have h := gap hL hLe
  norm_num [cert] at h ⊢
  exact h

end GaugeGaps.Z3Seed
