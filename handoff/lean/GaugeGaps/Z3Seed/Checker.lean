import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

/-!
# Integer checker for the `ℤ₃` gauge–Higgs ring

Configurations of a ring of `n` links are indices `s < 3^n` (digit `j` of `s` in base three is the
link `j`), and vectors are lists of integers. `applyH e κ n v s` is the entry `s` of `2 H v` for
integer couplings, so every quantity below is an integer and `decide +kernel` evaluates it.
The layout follows `SeedKernel/Ising/Checker.lean` of the CertifiedGaps library.
-/

namespace GaugeGaps.Z3Seed

/-- Digit `j` of `s` in base three. -/
def digit (s j : ℕ) : ℕ := s / 3 ^ j % 3

/-- The index `s` with digit `j` shifted by `a` modulo three. -/
def shiftN (s j a : ℕ) : ℕ := s - digit s j * 3 ^ j + (digit s j + a) % 3 * 3 ^ j

/-- Entry `s` of an integer vector. -/
def entry (v : List ℤ) (s : ℕ) : ℤ := v.getD s 0

/-- The diagonal of `D = diag(2, -1, -1)`. -/
def dZ (d : ℕ) : ℤ := if d = 0 then 2 else -1

/-- `∑ⱼ D(σⱼ)` for the configuration `s`. -/
def diagSum (n s : ℕ) : ℤ := (List.range n).foldl (fun a j ↦ a + dZ (digit s j)) 0

/-- Entry `s` of `2 H v`. -/
def applyH (eZ κZ : ℤ) (n : ℕ) (v : List ℤ) (s : ℕ) : ℤ :=
  -(κZ * diagSum n s * entry v s) -
    eZ * (List.range n).foldl
      (fun a j ↦ a + (entry v (shiftN s j 1) + entry v (shiftN s j 2))) 0 -
    (List.range n).foldl
      (fun a j ↦ a + (entry v (shiftN (shiftN s j 1) ((j + 1) % n) 2) +
        entry v (shiftN (shiftN s j 2) ((j + 1) % n) 1))) 0

/-- `‖v‖²`. -/
def dot (n : ℕ) (v : List ℤ) : ℤ :=
  (List.range (3 ^ n)).foldl (fun a s ↦ a + entry v s ^ 2) 0

/-- `‖S (2 H v) - lam v‖²`, the residual of `v` against `θ = lam / (2 S)` scaled by `(2 S)²`. -/
def residualSq (eZ κZ S : ℤ) (n : ℕ) (v : List ℤ) (lam : ℤ) : ℤ :=
  (List.range (3 ^ n)).foldl
    (fun a s ↦ a + (S * applyH eZ κZ n v s - lam * entry v s) ^ 2) 0

end GaugeGaps.Z3Seed
