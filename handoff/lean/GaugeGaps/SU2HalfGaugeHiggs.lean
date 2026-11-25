import CertifiedGaps.Ring.Gap
import CertifiedGaps.ChainCheck
import GaugeGaps.RatMat

/-!
# The `SU(2)` lattice gauge–Higgs chain with flux cutoff `1/2` as a reflection-positive ring

One-dimensional `SU(2)` lattice gauge theory with `SU(2)`-valued matter, in unitary gauge, with every link
restricted to electric flux `j ≤ 1/2`. A link state is a function of the group element
`w = a₀ + i a·σ` in the span of `1, 2a₀, 2a₁, 2a₂, 2a₃` (an orthonormal real basis of the `j = 0` and
`j = 1/2` blocks of `L²(SU(2))`), so the local dimension is `5` and every matrix is rational.

`H_L = ∑ₗ [e' Cₗ + m' (S^Rₗ + S^Lₗ₊₁)² - (κ/2) Tₗ]`, `e' = 4e/3`, `m' = 4/3`,

with `C = j(j+1)`, `T` multiplication by `tr w` compressed to `j ≤ 1/2`, and `S^R`, `S^L` the generators of
right and left multiplication: `i S^R_c = K^R_c / 2`, `i S^L_c = K^L_c / 2` for real antisymmetric integer
matrices `K^R_c`, `K^L_c`. Splitting the square gives the on-site term `(e + 2) Π - (κ/2) T` (`Π` the
projection on `j = 1/2`) and the bond `-(2/3) ∑_c K^R_c ⊗ K^L_c`. The inversion `w ↦ w⁻¹` acts as
`R = diag(1, 1, -1, -1, -1)` and `R K^R_c R = K^L_c`, so the bond is `-(2/3) ∑_c K^R_c ⊗ R K^R_c R`: the
reflection-positive form with antisymmetric factors. The weight `2/3 = (2/3)² + (1/3)² + (1/3)²` is written
with three copies of each factor.
-/

open Matrix Real CertifiedGaps

namespace GaugeGaps.SU2HalfGaugeHiggs

/-- `K^R_c`: twice `i` times the generator of right multiplication, on `(1, a₀, a₁, a₂, a₃)`. -/
def KR : Fin 3 → Matrix (Fin 5) (Fin 5) ℤ := ![
  !![0, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, -1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, -1, 0],
  !![0, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, -1; 0, -1, 0, 0, 0; 0, 0, 1, 0, 0],
  !![0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0; 0, 0, -1, 0, 0; 0, -1, 0, 0, 0]]
/-- `K^L_c`: twice `i` times the generator of left multiplication. -/
def KL : Fin 3 → Matrix (Fin 5) (Fin 5) ℤ := ![
  !![0, 0, 0, 0, 0; 0, 0, -1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, -1, 0],
  !![0, 0, 0, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, -1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0],
  !![0, 0, 0, 0, 0; 0, 0, 0, 0, -1; 0, 0, 0, 1, 0; 0, 0, -1, 0, 0; 0, 1, 0, 0, 0]]
/-- The inversion `w ↦ w⁻¹`. -/
def Rq : Matrix (Fin 5) (Fin 5) ℤ := !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, -1, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, -1]
/-- The projection on the `j = 1/2` block. -/
def Pq : Matrix (Fin 5) (Fin 5) ℤ := !![0, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
/-- Multiplication by `tr w`, compressed to `j ≤ 1/2`. -/
def Tq : Matrix (Fin 5) (Fin 5) ℤ := !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]

theorem KR_transpose : ∀ c, (KR c)ᵀ = -KR c := by decide +kernel
theorem Pq_transpose : Pqᵀ = Pq := by decide +kernel
theorem Tq_transpose : Tqᵀ = Tq := by decide +kernel
theorem Rq_transpose : Rqᵀ = Rq := by decide +kernel
theorem Rq_sq : Rq * Rq = 1 := by decide +kernel
theorem Rq_Pq : Rq * Pq * Rq = Pq := by decide +kernel
theorem Rq_Tq : Rq * Tq * Rq = Tq := by decide +kernel
/-- The inversion exchanges right and left multiplication. -/
theorem Rq_KR : ∀ c, Rq * KR c * Rq = KL c := by decide +kernel
/-- Left and right generators commute. -/
theorem KR_KL_comm : ∀ c d, KR c * KL d = KL d * KR c := by decide +kernel
/-- Each generator squares to `-1` on the `j = 1/2` block: the spin is `1/2`. -/
theorem KR_sq : ∀ c, KR c * KR c = -Pq := by decide +kernel

/-- The scalars of the three copies of each bond factor: `(2/3)² + (1/3)² + (1/3)² = 2/3`. -/
noncomputable def copyWeight : Fin 3 → ℝ := ![2 / 3, 1 / 3, 1 / 3]

/-- The `SU(2)` gauge–Higgs chain with flux cutoff `1/2`, electric coupling `e` and hopping `κ`, as a
reflection-positive ring with internal reflection `R`. -/
noncomputable def model (e κ : ℝ) : RPRing (Fin 5) (Fin 3 × Fin 3) where
  C α := copyWeight α.2 • castM (KR α.1)
  o := (e + 2) • castM Pq - (κ / 2) • castM Tq
  C_symm α := by
    right; rw [transpose_smul, castM_transpose, KR_transpose, castM_neg, smul_neg]
  o_symm := by
    simp [transpose_sub, transpose_smul, castM_transpose, Pq_transpose, Tq_transpose]
  refl := castM Rq
  refl_symm := by rw [castM_transpose, Rq_transpose]
  refl_sq := by rw [← castM_mul, Rq_sq, castM_one]
  refl_o := by
    have hP : castM Rq * castM Pq * castM Rq = castM Pq := by rw [castM_conj, Rq_Pq]
    have hT : castM Rq * castM Tq * castM Rq = castM Tq := by rw [castM_conj, Rq_Tq]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, hP, hT]

/-- A certified point: the couplings, the seed inverse temperature `β₀` (the seed length is `n₀ = 2`)
and the chain certificate, whose first entries are the seed defects. -/
structure Point where
  /-- The electric coupling. -/
  e : ℚ
  /-- The hopping (Higgs) coupling. -/
  κ : ℚ
  /-- The seed inverse temperature. -/
  β₀ : ℚ
  /-- The chain certificate. -/
  cert : ChainCertificate

/-- The certified points (`models/su2_gauge_higgs_half`). -/
def points : List Point := [
  -- bound ≈ 1.2503
  ⟨1, 1, 23 / 8, {
    s := [1027e-5, 3428e-7, 2771e-10, 1574e-16, 4958e-29, 4917e-54, 4836e-104, 4678e-204, 4377e-404]
    t := [5186e-6, 5832e-8, 6837e-12, 935e-19, 1749e-35, 6119e-67, 7489e-130, 1122e-255, 2518e-507]
    r := 364e-1
    ε := 4377e-404 }⟩,
  -- bound ≈ 1.4980
  ⟨1, 1 / 2, 15 / 4, {
    s := [1577e-6, 6376e-9, 8569e-14, 1473e-23, 434e-42, 3768e-82, 284e-159, 1614e-316, 521e-628]
    t := [4079e-7, 3385e-10, 2293e-16, 1052e-28, 2214e-53, 9804e-103, 1923e-201, 7396e-399, 1095e-793]
    r := 2752e-1
    ε := 521e-628 }⟩,
  -- bound ≈ 2.2454
  ⟨2, 1, 5 / 2, {
    s := [8785e-7, 4564e-9, 7586e-14, 1481e-23, 4636e-43, 4312e-82, 3719e-160, 2767e-316, 1532e-628]
    t := [1258e-6, 3189e-9, 2035e-14, 8283e-25, 1373e-45, 3771e-87, 2845e-170, 1619e-336, 5243e-669]
    r := 2741e-1
    ε := 1532e-628 }⟩,
  -- bound ≈ 1.8492
  ⟨2, 2, 2 / 1, {
    s := [7547e-6, 2469e-7, 1752e-10, 6831e-17, 9434e-30, 1781e-55, 6344e-107, 805e-209, 1297e-415]
    t := [68e-4, 9787e-8, 192e-10, 7373e-19, 1088e-33, 2368e-63, 1122e-122, 2518e-241, 1269e-478]
    r := 4038e-2
    ε := 1297e-415 }⟩,
  -- bound ≈ 3.8894
  ⟨4, 1, 17 / 8, {
    s := [6775e-8, 241e-10, 1943e-18, 9183e-33, 1746e-61, 6105e-119, 7455e-234, 1112e-463, 2474e-923]
    t := [8401e-8, 1413e-11, 3994e-19, 3191e-34, 2037e-64, 8299e-125, 1378e-245, 3798e-487, 2885e-970]
    r := 3885
    ε := 2474e-923 }⟩]

/-- All certificates are valid, checked by the kernel. -/
theorem points_valid : ∀ p ∈ points, p.cert.Valid := by decide +kernel

/-- Every seed inverse temperature is positive. -/
theorem points_β₀_pos : ∀ p ∈ points, 0 < p.β₀ := by decide +kernel

/-- The seed inequalities, certified outside Lean by the CertifiedGaps Julia core. -/
def Seeds : Prop := ∀ p ∈ points,
    1 - (p.cert.sAt 0 : ℝ) ≤ (model p.e p.κ).spatialPurity 2 p.β₀ ∧
      1 - (p.cert.tAt 0 : ℝ) ≤ (model p.e p.κ).thermalPurity 4 p.β₀

/-- **The `SU(2)` gauge–Higgs chain with flux cutoff `1/2`.** Given the seeds, at every certified point
every even ring of `L ≥ 2` links has a unique ground state and gap `Δ_L > log r / β₀`. -/
theorem gap (hseeds : Seeds) {p : Point} (hp : p ∈ points) {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT ((model p.e p.κ).spectrum L) (log (p.cert.r : ℝ) / p.β₀) :=
  (model p.e p.κ).gapGT_of_chainCertificate (n₀ := 2) (by norm_num) (by decide)
    (by exact_mod_cast points_β₀_pos p hp) (points_valid p hp) ⟨rfl, rfl, rfl⟩ (hseeds p hp).1
    (hseeds p hp).2 hL hLe

end GaugeGaps.SU2HalfGaugeHiggs
