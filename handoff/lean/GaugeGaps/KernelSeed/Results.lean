import GaugeGaps.KernelSeed.SU2HalfE2K1Fine
import GaugeGaps.KernelSeed.SU2HalfE4K1Fine
import GaugeGaps.KernelSeed.SU2HalfE1K1Fine
import GaugeGaps.KernelSeed.SU2HalfE3K2Fine
import GaugeGaps.KernelSeed.S3E1K24Fine

/-!
# Spectral gaps with no hypothesis: the statements

Each theorem says: on every ring of even length `L ≥ 2` the Hamiltonian has a nondegenerate lowest
eigenvalue and every other eigenvalue lies more than the stated constant above it. The seeds are
proved from kernel computations (`KernelSeed/`), so nothing is assumed and no numerics outside
Lean enter. `#print axioms` at the end lists the axioms.
-/

open CertifiedGaps

namespace GaugeGaps

/-- `SU(2)` gauge–Higgs chain, flux cutoff `1/2`, `m = 1`, `e = 2`, `κ = 1`: gap `> 1.3042`. -/
theorem su2_half_gap_e2_k1 {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT ((SU2HalfGaugeHiggs.model 2 1).spectrum L) (Real.log 217 / (33 / 8)) := by
  have h := SU2HalfSeed.E2K1.gap_fine hL hLe
  norm_num [SU2HalfSeed.E2K1.certFine] at h ⊢
  exact h

/-- `SU(2)` gauge–Higgs chain, flux cutoff `1/2`, `m = 1`, `e = 4`, `κ = 1`: gap `> 2.7142`. -/
theorem su2_half_gap_e4_k1 {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT ((SU2HalfGaugeHiggs.model 4 1).spectrum L) (Real.log 1744 / (11 / 4)) := by
  have h := SU2HalfSeed.E4K1.gap_fine hL hLe
  norm_num [SU2HalfSeed.E4K1.certFine] at h ⊢
  exact h

/-- `SU(2)` gauge–Higgs chain, flux cutoff `1/2`, `m = 1`, `e = 1`, `κ = 1`: gap `> 0.5648`. -/
theorem su2_half_gap_e1_k1 {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT ((SU2HalfGaugeHiggs.model 1 1).spectrum L) (Real.log (2082 / 100) / (43 / 8)) := by
  have h := SU2HalfSeed.E1K1.gap_fine hL hLe
  norm_num [SU2HalfSeed.E1K1.certFine] at h ⊢
  exact h

/-- `SU(2)` gauge–Higgs chain, flux cutoff `1/2`, `m = 1`, `e = 3`, `κ = 2`: gap `> 0.9515`. -/
theorem su2_half_gap_e3_k2 {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT ((SU2HalfGaugeHiggs.model 3 2).spectrum L) (Real.log (6426 / 100) / (35 / 8)) := by
  have h := SU2HalfSeed.E3K2.gap_fine hL hLe
  norm_num [SU2HalfSeed.E3K2.certFine] at h ⊢
  exact h

/-- `S₃` gauge–Higgs chain, `e = 1`, `κ = 24`: gap `> 6.1519`. -/
theorem s3_gap_e1_k24 {L : ℕ} (hL : 2 ≤ L) (hLe : Even L) :
    GapGT ((S3GaugeHiggs.model 1 24).spectrum L) (Real.log (2167 / 100) / (1 / 2)) := by
  have h := S3Seed.E1K24.gap_fine hL hLe
  norm_num [S3Seed.E1K24.certFine] at h ⊢
  exact h

end GaugeGaps

#print axioms GaugeGaps.su2_half_gap_e2_k1
#print axioms GaugeGaps.su2_half_gap_e4_k1
#print axioms GaugeGaps.su2_half_gap_e1_k1
#print axioms GaugeGaps.su2_half_gap_e3_k2
#print axioms GaugeGaps.s3_gap_e1_k24
