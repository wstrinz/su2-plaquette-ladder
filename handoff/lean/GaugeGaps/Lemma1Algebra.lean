import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The algebraic core of Lemma 1 (split-link positivity)

Lemma 1 of the note has an analytic part (functions on `SU(2)^5`, complex conjugation, Casimirs) and an algebraic
part: the reflection `ρ` of a cell, what it does to translations and to the plaquette variable, and the identity
`tr (Q P⁻¹) = 2 Σ q_k p_k` with all four signs plus. A slip of orientation or sign in the algebraic part is the
realistic way the lemma could be wrong, so that part is checked here, for an arbitrary group where possible.

A cell has five link variables `(b', b'', t', t'', r)`: `b'` runs from the midpoint of the incoming bottom leg to the
bottom vertex, `b''` from the bottom vertex to the midpoint of the outgoing bottom leg, `t'`, `t''` likewise on
top, and `r` from the bottom vertex to the top vertex. A gauge transformation `g` at a vertex multiplies a link
that starts there by `g` on the left and a link that ends there by `g⁻¹` on the right.
-/

namespace GaugeGaps.Lemma1

/-- A cell configuration `(b', b'', t', t'', r)`. -/
@[ext] structure Cell (G : Type*) where
  bp : G
  bpp : G
  tp : G
  tpp : G
  r : G

variable {G : Type*} [Group G]

/-- The reflection of a cell: `ρ(b', b'', t', t'', r) = (b''⁻¹, b'⁻¹, t''⁻¹, t'⁻¹, r)`. -/
def rho (c : Cell G) : Cell G := ⟨c.bpp⁻¹, c.bp⁻¹, c.tpp⁻¹, c.tp⁻¹, c.r⟩

@[simp] theorem rho_rho (c : Cell G) : rho (rho c) = c := by
  cases c; simp [rho]

/-- Gauge transformation at the bottom vertex. -/
def gaugeBot (g : G) (c : Cell G) : Cell G := ⟨c.bp * g⁻¹, g * c.bpp, c.tp, c.tpp, g * c.r⟩

/-- Gauge transformation at the top vertex. -/
def gaugeTop (g : G) (c : Cell G) : Cell G := ⟨c.bp, c.bpp, c.tp * g⁻¹, g * c.tpp, c.r * g⁻¹⟩

/-- `ρ` commutes with the vertex gauge transformations, so `ψ ↦ ψ ∘ ρ` preserves gauge-invariant functions. -/
theorem rho_gaugeBot (g : G) (c : Cell G) : rho (gaugeBot g c) = gaugeBot g (rho c) := by
  cases c; simp [rho, gaugeBot]

theorem rho_gaugeTop (g : G) (c : Cell G) : rho (gaugeTop g c) = gaugeTop g (rho c) := by
  cases c; simp [rho, gaugeTop]

/-- The plaquette variable carried by the outgoing half of a cell: `P = b''⁻¹ r t''`. -/
def P (c : Cell G) : G := c.bpp⁻¹ * c.r * c.tpp

/-- The plaquette variable carried by the incoming half of a cell: `Q = b' r t'⁻¹`. -/
def Q (c : Cell G) : G := c.bp * c.r * c.tp⁻¹

theorem P_rho (c : Cell G) : P (rho c) = Q c := by
  cases c; simp [rho, P, Q]

theorem Q_rho (c : Cell G) : Q (rho c) = P c := by
  cases c; simp [rho, P, Q]

theorem P_gaugeBot (g : G) (c : Cell G) : P (gaugeBot g c) = P c := by
  cases c; simp [P, gaugeBot, mul_assoc]

theorem P_gaugeTop (g : G) (c : Cell G) : P (gaugeTop g c) = P c := by
  cases c; simp [P, gaugeTop, mul_assoc]

theorem Q_gaugeBot (g : G) (c : Cell G) : Q (gaugeBot g c) = Q c := by
  cases c; simp [Q, gaugeBot, mul_assoc]

theorem Q_gaugeTop (g : G) (c : Cell G) : Q (gaugeTop g c) = Q c := by
  cases c; simp [Q, gaugeTop, mul_assoc]

/-- The holonomy of the plaquette between cell `c` and the next cell `d`, with the legs rejoined:
`b = b''(c) b'(d)`, `t = t''(c) t'(d)`, `U = b r(d) t⁻¹ r(c)⁻¹`. -/
def plaquette (c d : Cell G) : G := (c.bpp * d.bp) * d.r * (c.tpp * d.tp)⁻¹ * c.r⁻¹

/-- The plaquette holonomy is conjugate to `Q(d) P(c)⁻¹`, so every class function of it (the trace) is a
function of `P` on one cell and `Q` on the next. -/
theorem plaquette_eq_conj (c d : Cell G) : plaquette c d = c.bpp * (Q d * (P c)⁻¹) * c.bpp⁻¹ := by
  cases c; cases d; simp [plaquette, P, Q, mul_assoc]

section functions

variable {α : Type*}

/-- The reflection on functions of a cell. -/
def refl (ψ : Cell G → α) : Cell G → α := fun c => ψ (rho c)

/-- Right translation in `b''`: `(R(h) ψ)(…, b'', …) = ψ(…, b'' h, …)`. -/
def rightBpp (h : G) (ψ : Cell G → α) : Cell G → α := fun c => ψ ⟨c.bp, c.bpp * h, c.tp, c.tpp, c.r⟩

/-- Left translation in `b'`: `(L(h) ψ)(b', …) = ψ(h⁻¹ b', …)`. -/
def leftBp (h : G) (ψ : Cell G → α) : Cell G → α := fun c => ψ ⟨h⁻¹ * c.bp, c.bpp, c.tp, c.tpp, c.r⟩

/-- Right translation in `t''`. -/
def rightTpp (h : G) (ψ : Cell G → α) : Cell G → α := fun c => ψ ⟨c.bp, c.bpp, c.tp, c.tpp * h, c.r⟩

/-- Left translation in `t'`. -/
def leftTp (h : G) (ψ : Cell G → α) : Cell G → α := fun c => ψ ⟨c.bp, c.bpp, h⁻¹ * c.tp, c.tpp, c.r⟩

@[simp] theorem refl_refl (ψ : Cell G → α) : refl (refl ψ) = ψ := by
  funext c; simp [refl]

/-- Step 3 of the proof: the reflection turns right translation by `h` in `b''` into left translation by the SAME
`h` in `b'`. Hence `R S^R_a(b'') R = S^L_a(b')` with a plus sign. -/
theorem refl_rightBpp_refl (h : G) (ψ : Cell G → α) : refl (rightBpp h (refl ψ)) = leftBp h ψ := by
  funext c; cases c; simp [refl, rightBpp, leftBp, rho]

theorem refl_rightTpp_refl (h : G) (ψ : Cell G → α) : refl (rightTpp h (refl ψ)) = leftTp h ψ := by
  funext c; cases c; simp [refl, rightTpp, leftTp, rho]

/-- Step 4 of the proof: conjugating multiplication by `f` with the reflection gives multiplication by `f ∘ ρ`.
With `f` a component of `P` this is the same component of `Q`, by `P_rho`. -/
theorem refl_mul_refl [Mul α] (f ψ : Cell G → α) :
    refl (fun c => f c * refl ψ c) = fun c => f (rho c) * ψ c := by
  funext c; simp [refl]

end functions

/-! ### The trace identity for `SU(2)` -/

open Matrix

/-- An element of `SU(2)` is `!![a, b; -conj b, conj a]`. -/
theorem su2_entries {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ specialUnitaryGroup (Fin 2) ℂ) :
    A 1 1 = star (A 0 0) ∧ A 1 0 = -star (A 0 1) := by
  rw [mem_specialUnitaryGroup_iff] at hA
  obtain ⟨hU, hdet⟩ := hA
  have h1 : star A * A = 1 := mem_unitaryGroup_iff'.mp hU
  have h2 : A * adjugate A = 1 := by rw [mul_adjugate, hdet, one_smul]
  have h3 : star A = adjugate A := by
    calc star A = star A * (A * adjugate A) := by rw [h2, mul_one]
      _ = adjugate A := by rw [← mul_assoc, h1, one_mul]
  have e00 := congrFun (congrFun h3 0) 0
  have e01 := congrFun (congrFun h3 0) 1
  simp only [star_apply, adjugate_fin_two, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at e00 e01
  refine ⟨e00.symm, ?_⟩
  have := congrArg star e01
  simpa using this

/-- For a unitary matrix the inverse is the conjugate transpose. -/
theorem inv_eq_star_of_mem_unitary {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ unitaryGroup (Fin 2) ℂ) :
    A⁻¹ = star A :=
  Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.mp hA)

/-- `tr (Q P⁻¹) = 2 (q₀ p₀ + q₃ p₃ + q₂ p₂ + q₁ p₁)` for `P, Q` in `SU(2)`, where `P = p₀ + i p·σ`, that is
`p₀ = Re P₀₀`, `p₃ = Im P₀₀`, `p₂ = Re P₀₁`, `p₁ = Im P₀₁`. The trace is real and all four signs are plus. -/
theorem trace_mul_inv_su2 {P Q : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ specialUnitaryGroup (Fin 2) ℂ)
    (hQ : Q ∈ specialUnitaryGroup (Fin 2) ℂ) :
    (Q * P⁻¹).trace = ((2 * ((Q 0 0).re * (P 0 0).re + (Q 0 0).im * (P 0 0).im
      + (Q 0 1).re * (P 0 1).re + (Q 0 1).im * (P 0 1).im) : ℝ) : ℂ) := by
  obtain ⟨p11, p10⟩ := su2_entries hP
  obtain ⟨q11, q10⟩ := su2_entries hQ
  rw [inv_eq_star_of_mem_unitary ((mem_specialUnitaryGroup_iff.mp hP).1)]
  simp only [trace_fin_two, mul_apply, Fin.sum_univ_two, star_apply, p11, p10, q11, q10]
  apply Complex.ext <;> simp <;> ring

end GaugeGaps.Lemma1
