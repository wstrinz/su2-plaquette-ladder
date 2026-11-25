import GaugeGaps.LadderEvenGtOne
import GaugeGaps.TensionIntervals

/-!
# Both winding sectors together: gap `> 1` for the union of the two spectra

`full_gap_gt_one` combines the two certificate lists. `Ep`, `Em` are the spectra of two sectors (for the ladder: winding
parity `+1` and `-1`) at one coupling. If that coupling lies in an interval `I` of the list of Theorem B and in an
interval `J` of the list of Theorem C, and the seed hypotheses of both hold, then on every even ring of length `L ≥ 2`
the union of the two spectra has a nondegenerate lowest level with all other levels more than `1` above it.

The coupling itself does not appear: the link between `I`, `J`, `t` and the Hamiltonian is in the hypotheses, which
are what the two numerical implementations establish (and Lemmas 1 to 5 of the note for the moment inequalities).
-/

open Real CertifiedGaps

namespace GaugeGaps.Full

set_option maxRecDepth 1000000 in
/-- Every certified string tension exceeds `1/2`, so two plaquettes of winding cost more than `1`. -/
theorem tension_gt_half : ∀ J ∈ Tension.intervals, (1 : ℚ) / 2 < J.σ := by decide +kernel

theorem full_gap_gt_one {ι : ℕ → Type*} [∀ L, Fintype (ι L)] [∀ L, Nonempty (ι L)]
    {κ : ℕ → Type*} [∀ L, Fintype (κ L)] [∀ L, Nonempty (κ L)]
    (Ep : (L : ℕ) → ι L → ℝ) (Em : (L : ℕ) → κ L → ℝ)
    (hZp : HasSpatialMomentBounds Ep 2) (hZm : HasSpatialMomentBounds Em 2)
    -- Theorem B seeds
    {I : LadderEven.Interval} (hI : I ∈ LadderEven.intervals)
    (hs : 1 - (I.cert.sAt 0 : ℝ) ≤ spatialPurity Ep 2 I.β₀)
    (hth : 1 - (I.cert.tAt 0 : ℝ) ≤ thermalPurity Ep (2 * 2) I.β₀)
    -- Theorem C inputs
    {J : Tension.TInterval} (hJ : J ∈ Tension.intervals) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hω : ∀ m, (1 - t) * (J.ωa : ℝ) + t * J.ωb ≤ Em 2 m)
    (hℓ : log (partitionFunction Ep 2 J.β₁) ≤ (1 - t) * (J.ℓa : ℝ) + t * J.ℓb)
    (hθ : ∃ m, Ep 2 m ≤ (1 - t) * (J.θa : ℝ) + t * J.θb)
    (hε : 1 - (J.ε : ℝ) ≤ spatialPurity Ep 2 J.β) {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT (Sum.elim (Ep L) (Em L)) 1 := by
  have h1 := LadderEven.gap_gt_one_on_interval Ep hZp hI hs hth hL hLe
  have hσ : (1 : ℝ) / 2 < J.σ := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (tension_gt_half J hJ)
    push_cast at h; linarith
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  refine StringTension.gapGT_sum h1 zero_le_one le_rfl (τ := L * J.σ) (by nlinarith) ?_
  intro m₀ hmin m
  obtain ⟨m₁, hmin₁, hb⟩ := Tension.tension_on_interval Ep Em hZp hZm hJ ht0 ht1 hω hℓ hθ hε hL hLe m
  have h2 : Ep L m₁ ≤ Ep L m₀ := hmin₁ m₀
  have h3 : Ep L m₀ ≤ Ep L m₁ := hmin m₁
  linarith

end GaugeGaps.Full
