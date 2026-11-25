import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases

/-!
# Integer matrices cast to the reals

Model matrices are written over `ℤ`, where matrix identities are decided by the kernel, and then
cast to `ℝ`. Real coefficients enter only as scalars.
-/

open Matrix

namespace GaugeGaps

variable {n : Type*}

/-- An integer matrix as a real matrix. -/
noncomputable def castM (M : Matrix n n ℤ) : Matrix n n ℝ := M.map (Int.castRingHom ℝ)

@[simp] theorem castM_apply (M : Matrix n n ℤ) (i j : n) : castM M i j = (M i j : ℝ) := rfl

theorem castM_transpose (M : Matrix n n ℤ) : (castM M)ᵀ = castM Mᵀ := rfl

theorem castM_mul [Fintype n] (M N : Matrix n n ℤ) : castM (M * N) = castM M * castM N :=
  Matrix.map_mul

theorem castM_one [DecidableEq n] : castM (1 : Matrix n n ℤ) = 1 := by
  simp [castM]

theorem castM_neg (M : Matrix n n ℤ) : castM (-M) = -castM M := by
  ext i j; simp

theorem castM_add (M N : Matrix n n ℤ) : castM (M + N) = castM M + castM N := by
  ext i j; simp

theorem castM_sub (M N : Matrix n n ℤ) : castM (M - N) = castM M - castM N := by
  ext i j; simp

/-- Conjugation by a cast matrix. -/
theorem castM_conj [Fintype n] (F M : Matrix n n ℤ) :
    castM F * castM M * castM F = castM (F * M * F) := by
  rw [castM_mul, castM_mul]

end GaugeGaps
