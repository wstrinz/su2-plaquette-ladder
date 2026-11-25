import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.Basic

/-!
# Integer checker for a ring with rational local matrices

`IntRing d` holds integer tables `den · o` and `den · bond` of a ring with local dimension `d`.
Configurations of `n` sites are indices `s < d^n` (digit `j` in base `d` is the site `j`), and an
integer vector is packed into one natural number, 48 bits per entry with bias `2^47`, as in
`SeedKernel/Ising/Checker.lean` of the CertifiedGaps library. `applyH` is the entry of `den · H v`,
`gershC` is `den` times the local Gershgorin function, and `classicalCount` counts the
configurations whose Gershgorin value lies below a cut. Everything is an integer, so
`decide +kernel` evaluates it.
-/

namespace GaugeGaps.KernelSeed

/-- Integer tables of a ring: the denominator, `den · o` and `den · bond`. -/
structure IntRing (d : ℕ) where
  /-- The common denominator. -/
  den : ℤ
  /-- `den` times the on-site matrix. -/
  o : Fin d → Fin d → ℤ
  /-- `den` times the bond matrix, `b a b' c e = den · ⟨a b'| h |c e⟩`. -/
  b : Fin d → Fin d → Fin d → Fin d → ℤ

variable {d : ℕ} [NeZero d]

/-- Digit `j` of `s` in base `d`. -/
def digitF (s j : ℕ) : Fin d := Fin.ofNat d (s / d ^ j)

/-- The index `s` with digit `j` replaced by `a`. -/
def setDigit (s j : ℕ) (a : Fin d) : ℕ := s - (digitF (d := d) s j).val * d ^ j + a.val * d ^ j

/-- Entry `s` of a packed integer vector. -/
def entry (v s : ℕ) : ℤ := Int.ofNat ((v >>> (48 * s)) % 2 ^ 48) - 2 ^ 47

/-- `t * u`, without evaluating `u` when `t = 0`. -/
def term (t u : ℤ) : ℤ := if t = 0 then 0 else t * u

theorem term_eq (t u : ℤ) : term t u = t * u := by
  unfold term
  split_ifs with h <;> simp [h]

/-- `‖v‖²` on `n` sites. -/
def dot (d n v : ℕ) : ℤ := (List.range (d ^ n)).foldl (fun a s ↦ a + entry v s ^ 2) 0

namespace IntRing

variable (M : IntRing d)

/-- Entry `s` of `den · H v` on a ring of `n` sites. -/
def applyH (n v s : ℕ) : ℤ :=
  ∑ j : Fin n, ∑ a : Fin d, ∑ b : Fin d,
      term (M.b (digitF s j) (digitF s ((j + 1) % n)) a b)
        (entry v (setDigit (setDigit s j a) ((j + 1) % n) b)) +
    ∑ j : Fin n, ∑ b : Fin d, term (M.o (digitF s j) b) (entry v (setDigit s j b))

/-- `‖S (den H v) - lam v‖²`: the residual of `v` against `θ = lam / (den S)`, times `(den S)²`. -/
def residualSq (S : ℤ) (n v : ℕ) (lam : ℤ) : ℤ :=
  (List.range (d ^ n)).foldl (fun a s ↦ a + (S * M.applyH n v s - lam * entry v s) ^ 2) 0

/-- The part of `residualSq` over the indices `lo ≤ s < lo + m`. Large rings are checked chunk by
chunk, one declaration each, which bounds the memory of the kernel. -/
def resChunk (S : ℤ) (n v : ℕ) (lam : ℤ) (lo m : ℕ) : ℤ :=
  (List.range m).foldl
    (fun a i ↦ a + (S * M.applyH n v (lo + i) - lam * entry v (lo + i)) ^ 2) 0

/-- `den` times the Gershgorin lower disc of the on-site matrix. -/
def gSiteZ (a : Fin d) : ℤ := M.o a a - ∑ b, if a = b then 0 else |M.o a b|

/-- `den` times the Gershgorin lower disc of the bond matrix. -/
def gBondZ (a b : Fin d) : ℤ :=
  M.b a b a b - ∑ c, ∑ e, if a = c ∧ b = e then 0 else |M.b a b c e|

/-- `den` times the local Gershgorin function of the configuration `s`. -/
def gershC (n s : ℕ) : ℤ :=
  ∑ j : Fin n, M.gBondZ (digitF s j) (digitF s ((j + 1) % n)) + ∑ j : Fin n, M.gSiteZ (digitF s j)

/-- The number of configurations with Gershgorin value below `cut / den`. -/
def classicalCount (n : ℕ) (cut : ℤ) : ℕ :=
  (List.range (d ^ n)).foldl (fun a s ↦ a + if M.gershC n s < cut then 1 else 0) 0

/-- The part of `classicalCount` over the indices `lo ≤ s < lo + m`. -/
def countChunk (n : ℕ) (cut : ℤ) (lo m : ℕ) : ℕ :=
  (List.range m).foldl (fun a i ↦ a + if M.gershC n (lo + i) < cut then 1 else 0) 0

end IntRing

end GaugeGaps.KernelSeed
