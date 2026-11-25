import GaugeGaps.LadderEvenGtOne

open Real CertifiedGaps GaugeGaps.LadderEven
namespace GaugeGaps.ExtendedGap

set_option maxRecDepth 1000000
def rows : List Interval := [
  -- rate 1.018006
  ⟨12, 121/10, 33/20, { s := [311e-4, 9052e-6, 4245e-7, 5895e-10, 8331e-16, 14301e-28, 4094e-51], t := [611e-4, 10477e-6, 236e-6, 11175e-11, 2498e-17, 12481e-31, 3116e-57], r := 5364e-3, ε := 4094e-51 }⟩,
  -- rate 1.008784
  ⟨121/10, 61/5, 33/20, { s := [315e-4, 931e-5, 4504e-7, 665e-9, 10614e-16, 23221e-28, 10794e-51], t := [619e-4, 10805e-6, 2515e-7, 12694e-11, 3223e-17, 20776e-31, 8633e-57], r := 5283e-3, ε := 10794e-51 }⟩,
  -- rate 1.005102
  ⟨61/5, 49/4, 33/20, { s := [317e-4, 9424e-6, 4616e-7, 6984e-10, 11706e-16, 28245e-28, 1597e-50], t := [622e-4, 10933e-6, 25769e-8, 13328e-11, 3553e-17, 2525e-30, 12752e-57], r := 5251e-3, ε := 1597e-50 }⟩,
  -- rate 0.965642
  ⟨49/4, 25/2, 33/20, { s := [335e-4, 1063e-5, 5952e-7, 11711e-10, 3309e-15, 22607e-27, 10232e-49], t := [657e-4, 12466e-6, 33844e-8, 2302e-10, 10599e-17, 22468e-30, 10097e-55], r := 492e-2, ε := 10232e-49 }⟩,
  -- rate 0.876064
  ⟨25/2, 13, 33/20, { s := [379e-4, 13932e-6, 10586e-7, 37904e-10, 3515e-14, 25625e-25, 1315e-44], t := [742e-4, 16782e-6, 631e-6, 8027e-10, 1289e-15, 3324e-27, 22098e-51], r := 4244e-3, ε := 1315e-44 }⟩,
  -- rate 0.824679
  ⟨13, 27/2, 33/20, { s := [406e-4, 16224e-6, 14696e-7, 7422e-9, 13605e-14, 3852e-23, 2973e-42], t := [794e-4, 1988e-5, 9036e-7, 1651e-9, 5453e-15, 59471e-27, 7074e-48], r := 3899e-3, ε := 2973e-42 }⟩,
  -- rate 0.768188
  ⟨27/2, 14, 33/20, { s := [437e-4, 19127e-6, 21043e-7, 15539e-9, 604e-12, 7627e-22, 11657e-40], t := [854e-4, 2394e-5, 13453e-7, 36765e-10, 27039e-15, 14623e-25, 42767e-46], r := 3552e-3, ε := 11657e-40 }⟩,
  -- rate 0.706642
  ⟨14, 29/2, 33/20, { s := [473e-4, 22826e-6, 31046e-7, 34707e-9, 30606e-13, 197e-19, 7781e-37], t := [922e-4, 29231e-6, 20759e-7, 8819e-9, 15561e-14, 48429e-24, 46908e-43], r := 3209e-3, ε := 7781e-37 }⟩,
  -- rate 0.638132
  ⟨29/2, 15, 33/20, { s := [514e-4, 276e-4, 4759e-6, 8461e-8, 18602e-12, 7344e-19, 10824e-34], t := [1001e-4, 3643e-5, 3378e-6, 23637e-9, 11184e-13, 25017e-22, 12518e-39], r := 2866e-3, ε := 10824e-34 }⟩,
  -- rate 0.562078
  ⟨15, 31/2, 33/20, { s := [562e-4, 3384e-5, 7589e-6, 22629e-8, 13724e-11, 40504e-18, 3298e-30], t := [1091e-4, 46223e-6, 57977e-7, 7112e-8, 10138e-12, 20556e-20, 8451e-35], r := 2528e-3, ε := 3298e-30 }⟩,
  -- rate 0.476474
  ⟨31/2, 16, 33/20, { s := [617e-4, 4201e-5, 1265e-5, 6786e-7, 12943e-10, 3684e-15, 2738e-26], t := [1194e-4, 599e-4, 10657e-6, 2499e-7, 12565e-11, 31577e-18, 19943e-31], r := 2195e-3, ε := 2738e-26 }⟩]

def floorRate (I : Interval) : ℚ :=
  if I.lb ≤ 49/4 then 1 else if I.lb ≤ 14 then 0.76 else 0.46

theorem valid : ∀ I ∈ rows, I.cert.Valid := by decide +kernel
theorem tiles : tilesB rows 12 16 = true := by decide +kernel
theorem rates : ∀ I ∈ rows, 0 < I.β₀ ∧
    gtOneB { I with β₀ := floorRate I * I.β₀ } = true := by decide +kernel

theorem gap {ι : ℕ → Type*} [∀ L, Fintype (ι L)] [∀ L, Nonempty (ι L)]
    (E : (L : ℕ) → ι L → ℝ) (hz : HasSpatialMomentBounds E 2) {I : Interval} (hi : I ∈ rows)
    (hs : 1 - (I.cert.sAt 0 : ℝ) ≤ spatialPurity E 2 I.β₀)
    (ht : 1 - (I.cert.tAt 0 : ℝ) ≤ thermalPurity E (2 * 2) I.β₀)
    {L : ℕ} (hL : 2 ≤ L) (he : Even L) : GapGT (E L) (floorRate I : ℝ) := by
  obtain ⟨hb, hr⟩ := rates I hi
  have hb' : (0 : ℝ) < I.β₀ := by exact_mod_cast hb
  have hf : 0 < floorRate I := by
    unfold floorRate
    split
    · norm_num
    · split <;> norm_num
  have hp : (0 : ℝ) < (floorRate I : ℝ) * I.β₀ := mul_pos (by exact_mod_cast hf) hb'
  have h := one_lt_of_gtOneB (I := { I with β₀ := floorRate I * I.β₀ }) hr
  change 1 < log (I.cert.r : ℝ) / ((floorRate I * I.β₀ : ℚ) : ℝ) at h
  rw [Rat.cast_mul, lt_div_iff₀ hp, one_mul] at h
  exact (gapGT_of_chainCertificate E (by norm_num) (by decide) hb' hz I.cert
    (valid I hi) hs ht hL he).mono ((lt_div_iff₀ hb').2 h).le

#print axioms gap
end GaugeGaps.ExtendedGap
