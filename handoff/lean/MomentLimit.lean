import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.OrderClosed

/-!
# The moment inequalities of the purity criterion pass to limits

`SpatialMomentBounds` below is a verbatim restatement of the structure of the same name in
`CertifiedGaps/PurityCriterion.lean` (github.com/LionSR/CertifiedGaps): the three inequalities on a
sequence of partition functions `Z : ℕ → ℝ` that the doubling argument uses.

* `SpatialMomentBounds.of_tendsto`: they are preserved by pointwise limits.
* `SpatialMomentBounds.of_add_tendsto_zero`: the "penalty limit". If `Z i L = Zphys L + R i L` with a
  remainder `R i L → 0` (charged sectors pushed up by a Gauss-law penalty), then `Zphys` satisfies them.
-/

open Filter Topology

/-- The three moment inequalities used by the doubling argument, at one inverse temperature. -/
structure SpatialMomentBounds (Z : ℕ → ℝ) (n₀ : ℕ) : Prop where
  sq_le : ∀ n, n₀ ≤ n → Even n → Z (2 * n) ≤ Z n ^ 2
  squaring : ∀ n, n₀ ≤ n → Even n →
    2 * (Z (2 * n) ^ 2 - Z (2 * (2 * n))) ≤ (Z n ^ 2 - Z (2 * n)) ^ 2
  le_rpow : ∀ p q, n₀ ≤ p → p ≤ q → Even p → Even q → Z q ≤ Z p ^ ((q : ℝ) / p)

/-- The moment inequalities pass to pointwise limits. -/
theorem SpatialMomentBounds.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {Zs : ι → ℕ → ℝ} {Z : ℕ → ℝ} {n₀ : ℕ}
    (h : ∀ i, SpatialMomentBounds (Zs i) n₀)
    (hlim : ∀ L, Tendsto (fun i ↦ Zs i L) l (𝓝 (Z L))) :
    SpatialMomentBounds Z n₀ where
  sq_le n hn he :=
    le_of_tendsto_of_tendsto' (hlim (2 * n)) ((hlim n).pow 2) fun i ↦ (h i).sq_le n hn he
  squaring n hn he :=
    le_of_tendsto_of_tendsto'
      ((((hlim (2 * n)).pow 2).sub (hlim (2 * (2 * n)))).const_mul 2)
      ((((hlim n).pow 2).sub (hlim (2 * n))).pow 2) fun i ↦ (h i).squaring n hn he
  le_rpow p q hp hpq hpe hqe :=
    le_of_tendsto_of_tendsto' (hlim q)
      ((hlim p).rpow_const (Or.inr (by positivity))) fun i ↦ (h i).le_rpow p q hp hpq hpe hqe

/-- Penalty limit: if every `Zs i` satisfies the moment inequalities and differs from `Z` by a
remainder that tends to zero, then `Z` satisfies them. -/
theorem SpatialMomentBounds.of_add_tendsto_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    {Zs R : ι → ℕ → ℝ} {Z : ℕ → ℝ} {n₀ : ℕ}
    (h : ∀ i, SpatialMomentBounds (Zs i) n₀)
    (hsplit : ∀ i L, Zs i L = Z L + R i L)
    (hR : ∀ L, Tendsto (fun i ↦ R i L) l (𝓝 0)) :
    SpatialMomentBounds Z n₀ :=
  SpatialMomentBounds.of_tendsto h fun L ↦ by
    have := (tendsto_const_nhds (x := Z L) (f := l)).add (hR L)
    simpa [hsplit] using this

/-- Gap bounds pass to limits: if two sequences of levels converge and stay more than `b` apart,
the limits are at least `b` apart. Used for the flux-cutoff limit (eigenvalues of compressions). -/
theorem gap_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {e₀ e₁ : ι → ℝ} {E₀ E₁ b : ℝ}
    (h : ∀ i, e₀ i + b < e₁ i) (h₀ : Tendsto e₀ l (𝓝 E₀)) (h₁ : Tendsto e₁ l (𝓝 E₁)) :
    E₀ + b ≤ E₁ :=
  le_of_tendsto_of_tendsto' (h₀.add_const b) h₁ fun i ↦ (h i).le
