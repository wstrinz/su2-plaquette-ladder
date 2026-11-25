import GaugeGaps.KernelSeed.Checker

/-!
# Integer checker for the classical tail

`tailWeight` is the integer `∑_s 2^(K - min(k_s, K))` over the configurations above the cut, where
`k_s = ⌊(g_s · mul - num0) / dv⌋` and `g_s` is the Gershgorin value. With the parameters chosen so
that `k_s log 2 ≤ β (g_s / den - a₀)`, the sum `∑_s e^{-β (g_s / den - a₀)}` is at most
`tailWeight / 2^K`.
-/

namespace GaugeGaps.KernelSeed

/-- The exponent `k = ⌊(g · mul - num0) / dv⌋₊`. -/
def tailExp (mul num0 dv g : ℤ) : ℕ := ((g * mul - num0) / dv).toNat

/-- The weight of one configuration: `0` below the cut and `2^(K - min(k, K))` above it. -/
def tailTerm (cut mul num0 dv : ℤ) (K : ℕ) (g : ℤ) : ℕ :=
  if g < cut then 0 else 2 ^ (K - min (tailExp mul num0 dv g) K)

namespace IntRing

variable {d : ℕ} [NeZero d] (M : IntRing d)

/-- `2^K` times the dyadic bound on the classical tail. -/
def tailWeight (n : ℕ) (cut mul num0 dv : ℤ) (K : ℕ) : ℕ :=
  (List.range (d ^ n)).foldl (fun a s ↦ a + tailTerm cut mul num0 dv K (M.gershC n s)) 0

/-- The part of `tailWeight` over the indices `lo ≤ s < lo + m`. -/
def tailChunk (n : ℕ) (cut mul num0 dv : ℤ) (K lo m : ℕ) : ℕ :=
  (List.range m).foldl (fun a i ↦ a + tailTerm cut mul num0 dv K (M.gershC n (lo + i))) 0

end IntRing

end GaugeGaps.KernelSeed
