import CertifiedGaps.PurityCriterion

/-!
# String tension from the moment inequalities (Lemma 6 of the note)

Let `Ep` and `Em` be the spectra of a ring Hamiltonian in two sectors (for the ladder: winding charge `+1` and
`-1`), each satisfying the three moment inequalities of the purity criterion from length `2` on. Suppose

* every level of `Em` on the ring of length `2` is at least `ω`;
* `log Z_2(β₁) ≤ ℓ₁` and some level of `Ep` on the ring of length `2` is at most `θ`;
* the spatial purity of `Ep` at length `2` and inverse temperature `β > β₁` is at least `1 - ε`.

Then for every even `L ≥ 2` every level of `Em` on the ring of length `L` exceeds the lowest level of `Ep` on that
ring by at least `σ L`, with
`σ = ω / 2 - (ℓ₁ / 2 + β θ / 2 + D) / (β - β₁)`, `D = -log (1 - ε) / 4 - log (1 - f ε) / 4`, `f ε = ε² / (2 (1 - ε)²)`.

Proof: `ℓ^p` monotonicity gives `E^-_L ≥ (L/2) ω` (let the temperature go to zero) and `log Z_L(β₁) ≤ (L/2) ℓ₁`;
the squaring inequality keeps the purity at lengths `2^k` above `1 - f ε`, so `log Z_L(β)` is at least
`L (log Z_2(β) / 2 - D)`; and `Z_L(β₁) ≥ e^{(β - β₁) E₀} Z_L(β)` for the lowest level `E₀`.
-/

open Real CertifiedGaps Finset

namespace GaugeGaps.StringTension

/-! ### One inverse temperature: consequences of the moment inequalities -/

section OneTemperature

variable {Z : ℕ → ℝ}

theorem squaringDefect_nonneg (x : ℝ) : 0 ≤ squaringDefect x := by
  unfold squaringDefect; positivity

/-- The squaring map does not increase a defect that is at most `1/2`. -/
theorem squaringDefect_le_self {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : squaringDefect x ≤ x := by
  unfold squaringDefect
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith [mul_nonneg h0 (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - x) (by linarith : (0 : ℝ) ≤ 1 - 2 * x))]

theorem defect_step (hpos : ∀ L, 0 < Z L) (hB : SpatialMomentBounds Z 2) {n : ℕ} (hn : 2 ≤ n)
    (hne : Even n) :
    1 - Z (2 * (2 * n)) / Z (2 * n) ^ 2 ≤ squaringDefect (1 - Z (2 * n) / Z n ^ 2) :=
  one_sub_div_le_squaringDefect (hpos n) (hpos (2 * n)) (hB.squaring n hn hne)

theorem two_le_two_pow (j : ℕ) : 2 ≤ 2 ^ (j + 2) := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem even_two_pow (j : ℕ) : Even (2 ^ (j + 2)) := by
  rw [Nat.even_pow]; exact ⟨by decide, by omega⟩

/-- From a seed purity `≥ 1 - ε` at length `2`, the purity at every length `2^(j+2)` is `≥ 1 - f ε`. -/
theorem purity_ge (hpos : ∀ L, 0 < Z L) (hB : SpatialMomentBounds Z 2) {ε : ℝ} (hε1 : ε < 1)
    (hε₁ : squaringDefect ε ≤ 1 / 2) (hseed : 1 - ε ≤ Z 4 / Z 2 ^ 2) (j : ℕ) :
    1 - squaringDefect ε ≤ Z (2 * 2 ^ (j + 2)) / Z (2 ^ (j + 2)) ^ 2 := by
  induction j with
  | zero =>
    have hP1 : Z 4 / Z 2 ^ 2 ≤ 1 :=
      (div_le_one (pow_pos (hpos 2) 2)).2 (hB.sq_le 2 le_rfl (by decide))
    have h : 1 - Z 8 / Z 4 ^ 2 ≤ squaringDefect (1 - Z 4 / Z 2 ^ 2) :=
      defect_step hpos hB (n := 2) le_rfl (by decide)
    have h2 := squaringDefect_le_of_le hP1 hseed hε1
    show 1 - squaringDefect ε ≤ Z 8 / Z 4 ^ 2
    linarith
  | succ j ih =>
    have hn := two_le_two_pow j
    have hne := even_two_pow j
    have hP1 : Z (2 * 2 ^ (j + 2)) / Z (2 ^ (j + 2)) ^ 2 ≤ 1 :=
      (div_le_one (pow_pos (hpos _) 2)).2 (hB.sq_le _ hn hne)
    have h := defect_step hpos hB hn hne
    have h2 := squaringDefect_le_of_le hP1 ih (by linarith)
    have h3 := squaringDefect_le_self (squaringDefect_nonneg ε) hε₁
    have e : 2 ^ (j + 1 + 2) = 2 * 2 ^ (j + 2) := by ring
    rw [e]
    linarith

/-- `log Z` at the lengths `2^(j+2)`. -/
theorem log_dyadic_ge (hpos : ∀ L, 0 < Z L) (hB : SpatialMomentBounds Z 2) {ε : ℝ} (hε1 : ε < 1)
    (hε₁ : squaringDefect ε ≤ 1 / 2) (hseed : 1 - ε ≤ Z 4 / Z 2 ^ 2) (j : ℕ) :
    2 ^ (j + 1) * log (Z 2) + 2 ^ j * log (1 - ε) + (2 ^ j - 1) * log (1 - squaringDefect ε)
      ≤ log (Z (2 ^ (j + 2))) := by
  induction j with
  | zero =>
    have h : (1 - ε) * Z 2 ^ 2 ≤ Z 4 := by rwa [le_div_iff₀ (pow_pos (hpos 2) 2)] at hseed
    have hl := Real.log_le_log (mul_pos (by linarith) (pow_pos (hpos 2) 2)) h
    rw [Real.log_mul (by linarith) (pow_pos (hpos 2) 2).ne', Real.log_pow] at hl
    show 2 ^ (0 + 1) * log (Z 2) + 2 ^ 0 * log (1 - ε) + (2 ^ 0 - 1) * log (1 - squaringDefect ε) ≤ log (Z 4)
    push_cast at hl
    norm_num
    linarith
  | succ j ih =>
    have hp := purity_ge hpos hB hε1 hε₁ hseed j
    have hd : (0 : ℝ) < 1 - squaringDefect ε := by linarith
    have h : (1 - squaringDefect ε) * Z (2 ^ (j + 2)) ^ 2 ≤ Z (2 * 2 ^ (j + 2)) := by
      rwa [le_div_iff₀ (pow_pos (hpos _) 2)] at hp
    have hl := Real.log_le_log (mul_pos hd (pow_pos (hpos _) 2)) h
    rw [Real.log_mul hd.ne' (pow_pos (hpos _) 2).ne', Real.log_pow] at hl
    push_cast at hl
    have e : 2 ^ (j + 1 + 2) = 2 * 2 ^ (j + 2) := by ring
    rw [e]
    have key : (2 : ℝ) ^ (j + 1 + 1) * log (Z 2) + 2 ^ (j + 1) * log (1 - ε)
        + (2 ^ (j + 1) - 1) * log (1 - squaringDefect ε)
        = 2 * (2 ^ (j + 1) * log (Z 2) + 2 ^ j * log (1 - ε) + (2 ^ j - 1) * log (1 - squaringDefect ε))
          + log (1 - squaringDefect ε) := by ring
    rw [key]
    linarith

/-- Lower bound on `log Z_L` for every even `L ≥ 2`. -/
theorem log_ge_of_even (hpos : ∀ L, 0 < Z L) (hB : SpatialMomentBounds Z 2) {ε : ℝ} (hε1 : ε < 1)
    (hε₁ : squaringDefect ε ≤ 1 / 2) (hseed : 1 - ε ≤ Z 4 / Z 2 ^ 2) {L : ℕ} (hL : 2 ≤ L)
    (hLe : Even L) :
    (L : ℝ) * (log (Z 2) / 2 + log (1 - ε) / 4 + log (1 - squaringDefect ε) / 4) ≤ log (Z L) := by
  have hq : L ≤ 2 ^ (L + 2) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hr := hB.le_rpow L (2 ^ (L + 2)) hL hq hLe (even_two_pow L)
  have hlog := Real.log_le_log (hpos _) hr
  rw [Real.log_rpow (hpos L)] at hlog
  push_cast at hlog
  have hd := log_dyadic_ge hpos hB hε1 hε₁ hseed L
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have h2pos : (0 : ℝ) < 2 ^ (L + 2) := by positivity
  have ha : log (1 - squaringDefect ε) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith [squaringDefect_nonneg ε])
  have h1 : (L : ℝ) * log (Z (2 ^ (L + 2))) ≤ 2 ^ (L + 2) * log (Z L) := by
    calc (L : ℝ) * log (Z (2 ^ (L + 2))) ≤ (L : ℝ) * ((2 : ℝ) ^ (L + 2) / L * log (Z L)) :=
          mul_le_mul_of_nonneg_left hlog hLpos.le
      _ = 2 ^ (L + 2) * log (Z L) := by field_simp
  have e1 : (2 : ℝ) ^ (L + 2) = 4 * 2 ^ L := by ring
  have e2 : (2 : ℝ) ^ (L + 1) = 2 * 2 ^ L := by ring
  rw [e2] at hd
  have hx : (2 : ℝ) ^ L * log (1 - squaringDefect ε) ≤ (2 ^ L - 1) * log (1 - squaringDefect ε) := by
    have : ((2 : ℝ) ^ L - 1) * log (1 - squaringDefect ε)
        = 2 ^ L * log (1 - squaringDefect ε) - log (1 - squaringDefect ε) := by ring
    linarith
  have h2 : (2 : ℝ) ^ (L + 2) * ((L : ℝ) * (log (Z 2) / 2 + log (1 - ε) / 4
      + log (1 - squaringDefect ε) / 4)) ≤ (L : ℝ) * log (Z (2 ^ (L + 2))) := by
    have e3 : (2 : ℝ) ^ (L + 2) * ((L : ℝ) * (log (Z 2) / 2 + log (1 - ε) / 4
        + log (1 - squaringDefect ε) / 4))
        = (L : ℝ) * (2 * 2 ^ L * log (Z 2) + 2 ^ L * log (1 - ε)
          + 2 ^ L * log (1 - squaringDefect ε)) := by rw [e1]; ring
    rw [e3]
    exact mul_le_mul_of_nonneg_left (by linarith) hLpos.le
  exact le_of_mul_le_mul_left (h2.trans h1) h2pos

/-- Upper bound on `log Z_L` for every even `L ≥ 2`. -/
theorem log_le_of_even (hpos : ∀ L, 0 < Z L) (hB : SpatialMomentBounds Z 2) {L : ℕ} (hL : 2 ≤ L)
    (hLe : Even L) : log (Z L) ≤ (L : ℝ) / 2 * log (Z 2) := by
  have hr := hB.le_rpow 2 L le_rfl hL (by decide) hLe
  have hlog := Real.log_le_log (hpos L) hr
  rw [Real.log_rpow (hpos 2)] at hlog
  push_cast at hlog
  exact hlog

end OneTemperature

/-! ### Spectra -/

section Spectra

variable {ι : ℕ → Type*} [∀ L, Fintype (ι L)] [∀ L, Nonempty (ι L)]

omit [∀ L, Nonempty (ι L)] in
theorem exp_le_partitionFunction (E : (L : ℕ) → ι L → ℝ) (L : ℕ) (β : ℝ) (m : ι L) :
    exp (-(β * E L m)) ≤ partitionFunction E L β :=
  Finset.single_le_sum (f := fun m ↦ exp (-(β * E L m))) (fun _ _ ↦ (exp_pos _).le) (mem_univ m)

/-- The lowest level on every even ring is at most `L` times a bound computed on the ring of length `2`. -/
theorem lowest_le (E : (L : ℕ) → ι L → ℝ) (hZ : HasSpatialMomentBounds E 2) {β₁ β ℓ₁ θ ε : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ < β) (hε1 : ε < 1) (hε₁ : squaringDefect ε ≤ 1 / 2)
    (h1 : log (partitionFunction E 2 β₁) ≤ ℓ₁) (hθ : ∃ m, E 2 m ≤ θ)
    (hseed : 1 - ε ≤ spatialPurity E 2 β) {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    ∃ m₀, (∀ m, E L m₀ ≤ E L m) ∧ E L m₀ ≤ (L : ℝ) * ((ℓ₁ / 2 + β * θ / 2 - log (1 - ε) / 4
      - log (1 - squaringDefect ε) / 4) / (β - β₁)) := by
  obtain ⟨m₀, hm₀⟩ := Finite.exists_min (E L)
  refine ⟨m₀, hm₀, ?_⟩
  have hβpos : 0 < β := hβ₁.trans hβ
  have hpos : ∀ b L, 0 < partitionFunction E L b := fun b L ↦ partitionFunction_pos E L b
  -- Z_L(β₁) ≥ e^{(β - β₁) E₀} Z_L(β)
  have hcmp : exp ((β - β₁) * E L m₀) * partitionFunction E L β ≤ partitionFunction E L β₁ := by
    unfold partitionFunction
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ ↦ ?_
    rw [← exp_add]
    apply exp_le_exp.mpr
    nlinarith [hm₀ m, mul_le_mul_of_nonneg_left (hm₀ m) (sub_nonneg.mpr hβ.le)]
  have hlog := Real.log_le_log (mul_pos (exp_pos _) (hpos β L)) hcmp
  rw [Real.log_mul (exp_pos _).ne' (hpos β L).ne', Real.log_exp] at hlog
  -- upper bound at β₁, lower bound at β
  have hup : log (partitionFunction E L β₁) ≤ (L : ℝ) / 2 * log (partitionFunction E 2 β₁) :=
    log_le_of_even (Z := fun L ↦ partitionFunction E L β₁) (fun L ↦ hpos β₁ L) (hZ β₁ hβ₁) hL hLe
  have hseed' : 1 - ε ≤ partitionFunction E 4 β / partitionFunction E 2 β ^ 2 := hseed
  have hlow : (L : ℝ) * (log (partitionFunction E 2 β) / 2 + log (1 - ε) / 4
      + log (1 - squaringDefect ε) / 4) ≤ log (partitionFunction E L β) :=
    log_ge_of_even (Z := fun L ↦ partitionFunction E L β) (fun L ↦ hpos β L) (hZ β hβpos)
      hε1 hε₁ hseed' hL hLe
  -- log Z_2(β) ≥ -β θ
  obtain ⟨m, hm⟩ := hθ
  have hz2 : -(β * θ) ≤ log (partitionFunction E 2 β) := by
    have h := Real.log_le_log (exp_pos _) (exp_le_partitionFunction E 2 β m)
    rw [Real.log_exp] at h
    nlinarith [mul_le_mul_of_nonneg_left hm hβpos.le]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hdiff : 0 < β - β₁ := sub_pos.mpr hβ
  rw [mul_div_assoc', le_div_iff₀ hdiff]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (L : ℝ) / 2),
    mul_le_mul_of_nonneg_left hz2 (by positivity : (0 : ℝ) ≤ (L : ℝ) / 2)]

/-- If every level on the ring of length `2` is at least `ω`, every level on an even ring of length `L` is at
least `(L/2) ω`. -/
theorem level_ge (E : (L : ℕ) → ι L → ℝ) (hZ : HasSpatialMomentBounds E 2) {ω : ℝ}
    (hω : ∀ m, ω ≤ E 2 m) {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) (m : ι L) :
    (L : ℝ) / 2 * ω ≤ E L m := by
  by_contra hcon
  rw [not_le] at hcon
  set δ := (L : ℝ) / 2 * ω - E L m with hδ
  have hδpos : 0 < δ := by linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set c := log (Fintype.card (ι 2) : ℝ) with hc
  have hcard : (1 : ℝ) ≤ (Fintype.card (ι 2) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc0 : 0 ≤ c := Real.log_nonneg hcard
  set b := (L : ℝ) / 2 * (c + 1) / δ with hb
  have hbpos : 0 < b := by positivity
  have hpos : ∀ L, 0 < partitionFunction E L b := fun L ↦ partitionFunction_pos E L b
  have hup : log (partitionFunction E L b) ≤ (L : ℝ) / 2 * log (partitionFunction E 2 b) :=
    log_le_of_even (Z := fun L ↦ partitionFunction E L b) hpos (hZ b hbpos) hL hLe
  -- Z_2(b) ≤ card * e^{-b ω}
  have hz2 : partitionFunction E 2 b ≤ (Fintype.card (ι 2) : ℝ) * exp (-(b * ω)) := by
    unfold partitionFunction
    have := Finset.sum_le_card_nsmul (univ : Finset (ι 2)) (fun m ↦ exp (-(b * E 2 m))) (exp (-(b * ω)))
      (fun m _ ↦ exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (hω m) hbpos.le]))
    simpa [nsmul_eq_mul] using this
  have hl2 : log (partitionFunction E 2 b) ≤ c - b * ω := by
    have h := Real.log_le_log (hpos 2) hz2
    rw [Real.log_mul (by positivity) (exp_pos _).ne', Real.log_exp] at h
    linarith
  have hlm : -(b * E L m) ≤ log (partitionFunction E L b) := by
    have h := Real.log_le_log (exp_pos _) (exp_le_partitionFunction E L b m)
    rwa [Real.log_exp] at h
  have hkey : b * δ ≤ (L : ℝ) / 2 * c := by
    have h3 : log (partitionFunction E L b) ≤ (L : ℝ) / 2 * (c - b * ω) :=
      hup.trans (mul_le_mul_of_nonneg_left hl2 (by positivity))
    have : b * δ = b * ((L : ℝ) / 2 * ω) - b * E L m := by rw [hδ]; ring
    nlinarith
  have hbδ : b * δ = (L : ℝ) / 2 * (c + 1) := by rw [hb]; field_simp
  nlinarith

end Spectra

/-! ### The string tension -/

section Tension

variable {ι : ℕ → Type*} [∀ L, Fintype (ι L)] [∀ L, Nonempty (ι L)]
  {κ : ℕ → Type*} [∀ L, Fintype (κ L)] [∀ L, Nonempty (κ L)]

/-- **Lemma 6.** Every level of `Em` on an even ring of length `L ≥ 2` exceeds the lowest level of `Ep` on that
ring by at least `σ L`. -/
theorem string_tension (Ep : (L : ℕ) → ι L → ℝ) (Em : (L : ℕ) → κ L → ℝ)
    (hZp : HasSpatialMomentBounds Ep 2) (hZm : HasSpatialMomentBounds Em 2) {β₁ β ℓ₁ θ ε ω : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ < β) (hε1 : ε < 1) (hε₁ : squaringDefect ε ≤ 1 / 2)
    (h1 : log (partitionFunction Ep 2 β₁) ≤ ℓ₁) (hθ : ∃ m, Ep 2 m ≤ θ)
    (hseed : 1 - ε ≤ spatialPurity Ep 2 β) (hω : ∀ m, ω ≤ Em 2 m) {L : ℕ} (hL : 2 ≤ L)
    (hLe : Even L) (m : κ L) :
    ∃ m₀, (∀ m', Ep L m₀ ≤ Ep L m') ∧
      (L : ℝ) * (ω / 2 - (ℓ₁ / 2 + β * θ / 2 - log (1 - ε) / 4 - log (1 - squaringDefect ε) / 4)
        / (β - β₁)) ≤ Em L m - Ep L m₀ := by
  obtain ⟨m₀, hmin, hle⟩ := lowest_le Ep hZp hβ₁ hβ hε1 hε₁ h1 hθ hseed hL hLe
  refine ⟨m₀, hmin, ?_⟩
  have hge := level_ge Em hZm hω hL hLe m
  linarith

/-- Two sectors together: if the first has a nondegenerate lowest level with gap `> g` and every level of the second
lies at least `τ` above that lowest level, the union of the two spectra has a nondegenerate lowest level with gap
`> c` for every `0 ≤ c ≤ g` with `c < τ`. -/
theorem gapGT_sum {α β : Type*} {e : α → ℝ} {f : β → ℝ} {g τ c : ℝ} (h : GapGT e g) (hc0 : 0 ≤ c)
    (hcg : c ≤ g) (hcτ : c < τ) (hf : ∀ m₀, (∀ m', e m₀ ≤ e m') → ∀ m, τ ≤ f m - e m₀) :
    GapGT (Sum.elim e f) c := by
  obtain ⟨m₀, hm₀⟩ := h
  have hmin : ∀ m', e m₀ ≤ e m' := by
    intro m'
    by_cases hm : m' = m₀
    · rw [hm]
    · linarith [hm₀ m' hm]
  refine ⟨Sum.inl m₀, ?_⟩
  rintro (a | b) hne
  · have ha : a ≠ m₀ := fun h ↦ hne (by rw [h])
    simp only [Sum.elim_inl]
    linarith [hm₀ a ha]
  · simp only [Sum.elim_inl, Sum.elim_inr]
    linarith [hf m₀ hmin b]

end Tension

end GaugeGaps.StringTension
