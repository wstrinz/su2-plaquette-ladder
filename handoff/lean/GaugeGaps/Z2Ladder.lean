import CertifiedGaps.Ring.Gap
import CertifiedGaps.ChainCheck
import GaugeGaps.RatMat

/-!
# The `ℤ₂` plaquette ladder with split links as a reflection-positive ring

Pure `ℤ₂` lattice gauge theory on a ladder one plaquette wide. Every leg link is cut at its midpoint. A
cell is the H-shape around one rung, with Gauss's law imposed at the two rung sites, so a cell state is a
function of three group elements `(B, T, P) ∈ ℤ₂³`: `B = b'' + b'` and `T = t'' + t'` are the two legs
through the cell and `P = b'' + r + t''` is the path up the rung seen from the left midpoints. Its mirror
image is `Q = B + P + T`. A Gauss-law penalty `μ` sits at the link midpoints:

`H_L = ∑ₓ o(x) - μ ∑ₓ [X_B(x) X_B X_P(x+1) + X_T(x) X_T X_P(x+1)] - λ ∑ₓ Z_Q(x) Z_P(x+1)`,
`o = (3e + 2μ) - (e/2)(X_B + X_B X_P + X_T + X_T X_P) - e X_P`.

Here `X` flips and `Z` reads the sign of the named variable. The middle sum is the midpoint penalty (its
constant part is in `o`) and the last sum is the plaquette term. On states obeying Gauss's law at every
midpoint the penalty vanishes and this is the Kogut–Susskind ladder with electric coupling `e` and
plaquette coupling `λ`.

The cell reflection `F : (B, T, P) ↦ (B, T, Q)` satisfies `F X_B F = X_B X_P`, `F X_T F = X_T X_P` and
`F Z_Q F = Z_P`, so the bond is `-∑ C ⊗ F C F` with `C ∈ {√μ X_B, √μ X_T, √λ Z_Q}`: the reflection-positive
form. Cell states are ordered as `(B, T, P) = 000, 001, 010, …, 111`.
-/

open Matrix Real CertifiedGaps

namespace GaugeGaps.Z2Ladder

/-- `X_B`: flip the bottom leg variable. -/
def XBq : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0]
/-- `X_T`: flip the top leg variable. -/
def XTq : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0]
/-- `X_P`: flip the rung path variable. -/
def XPq : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 0]
/-- `Z_Q`: the sign of the mirror path `Q = B + P + T`. -/
def ZQq : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, -1]
/-- `Z_P`: the sign of the path `P`. -/
def ZPq : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, -1]
/-- The cell reflection `(B, T, P) ↦ (B, T, B + P + T)`. -/
def Fq : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 1]
/-- `X_B + X_B X_P + X_T + X_T X_P`: the four half-link electric hops. -/
def Hopq : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, 1, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 1, 0, 0; 1, 1, 0, 0, 0, 0, 1, 1; 1, 1, 0, 0, 0, 0, 1, 1; 1, 1, 0, 0, 0, 0, 1, 1; 1, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 1, 0, 0]

theorem XBq_transpose : XBqᵀ = XBq := by decide +kernel
theorem XTq_transpose : XTqᵀ = XTq := by decide +kernel
theorem XPq_transpose : XPqᵀ = XPq := by decide +kernel
theorem ZQq_transpose : ZQqᵀ = ZQq := by decide +kernel
theorem Hopq_transpose : Hopqᵀ = Hopq := by decide +kernel
theorem Fq_transpose : Fqᵀ = Fq := by decide +kernel
theorem Fq_sq : Fq * Fq = 1 := by decide +kernel
theorem Fq_one : Fq * 1 * Fq = 1 := by decide +kernel
theorem Fq_Hopq : Fq * Hopq * Fq = Hopq := by decide +kernel
theorem Fq_XPq : Fq * XPq * Fq = XPq := by decide +kernel
/-- The reflected leg flips are the midpoint gauge transformations seen from the next cell. -/
theorem Fq_XBq : Fq * XBq * Fq = XBq * XPq := by decide +kernel
theorem Fq_XTq : Fq * XTq * Fq = XTq * XPq := by decide +kernel
/-- The mirror image of the path `Q` is the path `P`. -/
theorem Fq_ZQq : Fq * ZQq * Fq = ZPq := by decide +kernel
/-- The hop matrix is the sum of the four half-link flips. -/
theorem Hopq_eq : Hopq = XBq + XBq * XPq + XTq + XTq * XPq := by decide +kernel

/-- The split-link `ℤ₂` plaquette ladder with electric coupling `e`, plaquette coupling `lam` and
midpoint Gauss penalty `μ`, as a reflection-positive ring with internal reflection `F`. -/
noncomputable def model (e lam μ : ℝ) : RPRing (Fin 8) (Fin 3) where
  C α := if α = 0 then √μ • castM XBq else if α = 1 then √μ • castM XTq else √lam • castM ZQq
  o := (3 * e + 2 * μ) • castM (1 : Matrix (Fin 8) (Fin 8) ℤ) - (e / 2) • castM Hopq - e • castM XPq
  C_symm α := by
    left
    by_cases h0 : α = 0
    · simp [h0, transpose_smul, castM_transpose, XBq_transpose]
    · by_cases h1 : α = 1
      · simp [h1, transpose_smul, castM_transpose, XTq_transpose]
      · simp [h0, h1, transpose_smul, castM_transpose, ZQq_transpose]
  o_symm := by
    simp [transpose_sub, transpose_smul, castM_transpose, Hopq_transpose, XPq_transpose]
  refl := castM Fq
  refl_symm := by rw [castM_transpose, Fq_transpose]
  refl_sq := by rw [← castM_mul, Fq_sq, castM_one]
  refl_o := by
    have h1 : castM Fq * castM (1 : Matrix (Fin 8) (Fin 8) ℤ) * castM Fq = castM 1 := by
      rw [castM_conj, Fq_one]
    have hH : castM Fq * castM Hopq * castM Fq = castM Hopq := by rw [castM_conj, Fq_Hopq]
    have hP : castM Fq * castM XPq * castM Fq = castM XPq := by rw [castM_conj, Fq_XPq]
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, h1, hH, hP]

/-- A certified point: the couplings, the seed inverse temperature `β₀` (the seed length is `n₀ = 2`
cells) and the chain certificate, whose first entries are the seed defects. -/
structure Point where
  /-- The electric coupling. -/
  e : ℚ
  /-- The plaquette coupling. -/
  lam : ℚ
  /-- The midpoint Gauss penalty. -/
  μ : ℚ
  /-- The seed inverse temperature. -/
  β₀ : ℚ
  /-- The chain certificate. -/
  cert : ChainCertificate

/-- The certified points (`models/plaquette_ladder`). -/
def points : List Point := [
  -- bound ≈ 2.2183
  ⟨1, 1, 4, 7 / 4, {
    s := [101e-4, 2107e-7, 8886e-11, 158e-16, 4993e-31, 4987e-58, 4975e-112, 4951e-220, 4903e-436]
    t := [1581e-8, 2938e-11, 109e-16, 7069e-31, 183e-56, 8648e-111, 1584e-217, 5034e-431, 5069e-858]
    r := 4852e-2
    ε := 4903e-436 }⟩,
  -- bound ≈ 2.8061
  ⟨1, 1 / 2, 4, 17 / 8, {
    s := [1278e-6, 3282e-9, 2155e-14, 9289e-25, 1726e-45, 5959e-87, 7102e-170, 1009e-335, 2037e-667]
    t := [7667e-10, 116e-13, 1002e-24, 4301e-45, 5334e-86, 6344e-168, 814e-331, 1326e-659, 3517e-1315]
    r := 3888e-1
    ε := 2037e-667 }⟩]

/-- All certificates are valid, checked by the kernel. -/
theorem points_valid : ∀ p ∈ points, p.cert.Valid := by decide +kernel

/-- Every seed inverse temperature is positive. -/
theorem points_β₀_pos : ∀ p ∈ points, 0 < p.β₀ := by decide +kernel

/-- The seed inequalities, certified outside Lean by the CertifiedGaps Julia core. -/
def Seeds : Prop := ∀ p ∈ points,
    1 - (p.cert.sAt 0 : ℝ) ≤ (model p.e p.lam p.μ).spatialPurity 2 p.β₀ ∧
      1 - (p.cert.tAt 0 : ℝ) ≤ (model p.e p.lam p.μ).thermalPurity 4 p.β₀

/-- **The split-link `ℤ₂` plaquette ladder.** Given the seeds, at every certified point every even ring
of `L ≥ 2` cells has a unique ground state and gap `Δ_L > log r / β₀`. -/
theorem gap (hseeds : Seeds) {p : Point} (hp : p ∈ points) {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT ((model p.e p.lam p.μ).spectrum L) (log (p.cert.r : ℝ) / p.β₀) :=
  (model p.e p.lam p.μ).gapGT_of_chainCertificate (n₀ := 2) (by norm_num) (by decide)
    (by exact_mod_cast points_β₀_pos p hp) (points_valid p hp) ⟨rfl, rfl, rfl⟩ (hseeds p hp).1
    (hseeds p hp).2 hL hLe

end GaugeGaps.Z2Ladder
