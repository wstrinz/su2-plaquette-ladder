import CertifiedGaps.PurityCriterion
import CertifiedGaps.ChainCheck

/-!
# The penalty limit

Let a family of spectra have the form `e + μ n` with `n ≥ 0` (a Hamiltonian `H₀ + μ N` with `N ≥ 0`
commuting with `H₀`, in a joint eigenbasis). As `μ → ∞` the partition functions converge to those of
the penalty-free levels `{i | n i = 0}`. Since the moment inequalities of the purity criterion pass to
limits (`SpatialMomentBounds.of_tendsto`, upstream), the penalty-free spectrum satisfies them as soon as
every penalised spectrum does, and the two-purity criterion applies to it directly.

For a lattice gauge theory, `N` is a Gauss-law penalty and the penalty-free levels are the
gauge-invariant sector.
-/

open Filter Topology Real Finset CertifiedGaps

namespace GaugeGaps

variable {ι : ℕ → Type*} [∀ L, Fintype (ι L)]

/-- The penalised spectrum `e + μ n`. -/
def penalised (e n : (L : ℕ) → ι L → ℝ) (μ : ℝ) : (L : ℕ) → ι L → ℝ :=
  fun L i ↦ e L i + μ * n L i

/-- The penalty-free indices. -/
abbrev Phys (n : (L : ℕ) → ι L → ℝ) (L : ℕ) : Type _ := {i : ι L // n L i = 0}

noncomputable instance (n : (L : ℕ) → ι L → ℝ) (L : ℕ) : Fintype (Phys n L) := Fintype.ofFinite _

/-- The penalty-free spectrum. -/
def physical (e n : (L : ℕ) → ι L → ℝ) : (L : ℕ) → Phys n L → ℝ :=
  fun L i ↦ e L i.1

/-- As the penalty grows, the partition function converges to that of the penalty-free levels. -/
theorem tendsto_partitionFunction_penalised (e n : (L : ℕ) → ι L → ℝ) (hn : ∀ L i, 0 ≤ n L i)
    (L : ℕ) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun μ : ℝ ↦ partitionFunction (penalised e n μ) L β) atTop
      (𝓝 (partitionFunction (physical e n) L β)) := by
  classical
  have hsum : partitionFunction (physical e n) L β =
      ∑ i : ι L, if n L i = 0 then exp (-(β * e L i)) else 0 := by
    rw [partitionFunction, ← Finset.sum_filter]
    exact (Finset.sum_subtype (p := fun i ↦ n L i = 0) (Finset.univ.filter fun i ↦ n L i = 0)
      (fun x ↦ by simp) (fun i ↦ exp (-(β * e L i)))).symm
  rw [hsum]
  unfold partitionFunction penalised
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  by_cases hi : n L i = 0
  · simp [hi]
  · have hpos : 0 < n L i := lt_of_le_of_ne (hn L i) (Ne.symm hi)
    simp only [hi, ite_false]
    have h1 : Tendsto (fun μ : ℝ ↦ μ * n L i) atTop atTop := tendsto_id.atTop_mul_const hpos
    have h2 : Tendsto (fun μ : ℝ ↦ β * (e L i + μ * n L i)) atTop atTop :=
      (tendsto_atTop_add_const_left _ _ h1).const_mul_atTop hβ
    exact tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2)

/-- **Penalty limit.** If every penalised spectrum satisfies the moment inequalities, so does the
penalty-free spectrum. -/
theorem hasSpatialMomentBounds_physical (e n : (L : ℕ) → ι L → ℝ) (hn : ∀ L i, 0 ≤ n L i) {n₀ : ℕ}
    (hn₀ : 0 < n₀) (h : ∀ μ : ℝ, 0 ≤ μ → HasSpatialMomentBounds (penalised e n μ) n₀) :
    HasSpatialMomentBounds (physical e n) n₀ := fun β hβ ↦
  SpatialMomentBounds.of_tendsto hn₀ ((eventually_ge_atTop (0 : ℝ)).mono fun μ hμ ↦ h μ hμ β hβ)
    fun L _ _ ↦ tendsto_partitionFunction_penalised e n hn L hβ

/-- **The two-purity criterion in the penalty-free sector.** If every penalised spectrum satisfies the
moment inequalities, then a valid chain certificate and the two seeds, computed in the penalty-free
sector alone, give the gap `Δ_L > log r / β₀` of the penalty-free spectrum on every even `L ≥ n₀`. -/
theorem gapGT_physical (e n : (L : ℕ) → ι L → ℝ) (hn : ∀ L i, 0 ≤ n L i)
    [∀ L, Nonempty (Phys n L)] {n₀ : ℕ} (hn₀ : 0 < n₀) (hn₀e : Even n₀) {β₀ : ℝ} (hβ₀ : 0 < β₀)
    (h : ∀ μ : ℝ, 0 ≤ μ → HasSpatialMomentBounds (penalised e n μ) n₀)
    (c : ChainCertificate) (hc : c.Valid)
    (hs : 1 - (c.sAt 0 : ℝ) ≤ spatialPurity (physical e n) n₀ β₀)
    (ht : 1 - (c.tAt 0 : ℝ) ≤ thermalPurity (physical e n) (2 * n₀) β₀)
    {L : ℕ} (hL : n₀ ≤ L) (hLe : Even L) :
    GapGT (physical e n L) (log (c.r : ℝ) / β₀) :=
  gapGT_of_chainCertificate (physical e n) hn₀ hn₀e hβ₀
    (hasSpatialMomentBounds_physical e n hn hn₀ h) c hc hs ht hL hLe

end GaugeGaps
