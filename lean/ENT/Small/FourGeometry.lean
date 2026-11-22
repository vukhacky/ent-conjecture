module

public import ENT.Small.LocalThresholds
public import ENT.Small.LocalDeficit

/-! Coefficient geometry and exact polynomial identities for the local n=4 proof. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Small
noncomputable section

theorem four_mean_le_half (a : Fin 4 → ℝ) (ha : IsUnit a)
    (ha0 : ∀ i, 0 ≤ a i) : coefficientMean a ≤ 1 / 2 := by
  have h := centeredEnergy_add_mean_sq (by decide : 0 < 4) a
  rw [ha] at h
  norm_num at h
  nlinarith [centeredEnergy_nonneg a, coefficientMean_nonneg a ha0]

theorem four_small_deficit_coordinate_lower (a : Fin 4 → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (hδ : deficit a ≤ 1 / 500) (i : Fin 4) :
    (1 : ℝ) / 5 < a i ^ 2 ∧ 9 / 10 < a i + 1 / 2 := by
  have hi : (a i ^ 2 - (4 : ℝ)⁻¹) ^ 2 ≤ deficit a :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a j ^ 2 - (4 : ℝ)⁻¹))
      (Finset.mem_univ i)
  norm_num at hi
  have hsq : (1 : ℝ) / 5 < a i ^ 2 := by nlinarith [ha0 i]
  exact ⟨hsq, by nlinarith [ha0 i]⟩

theorem four_centeredEnergy_le_deficit (a : Fin 4 → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (hδ : deficit a ≤ 1 / 500) :
    centeredEnergy a ≤ (100 / 81 : ℝ) * deficit a := by
  have hsum : (81 / 100 : ℝ) * (∑ i, (a i - 1 / 2) ^ 2) ≤ deficit a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := (four_small_deficit_coordinate_lower a ha0 hδ i).2
    have hsq : (81 : ℝ) / 100 ≤ (a i + 1 / 2) ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq (sq_nonneg (a i - 1 / 2))
    change (81 / 100 : ℝ) * (a i - 1 / 2) ^ 2 ≤ (a i ^ 2 - (4 : ℝ)⁻¹) ^ 2
    norm_num
    nlinarith
  have hc := centeredEnergy_le_sum_sq_shift (by decide : 0 < 4) a (1 / 2)
  linarith

theorem four_local_radius_le (a : Fin 4 → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (hδ : deficit a ≤ 1 / 500) :
    Real.sqrt (centeredEnergy a) ≤ 1 / 20 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · norm_num
  · have h := four_centeredEnergy_le_deficit a ha0 hδ
    nlinarith

theorem four_deficit_le_centeredEnergy (a : Fin 4 → ℝ) (ha : IsUnit a)
    (ha0 : ∀ i, 0 ≤ a i) : deficit a ≤ (9 / 4 : ℝ) * centeredEnergy a := by
  have hmean := four_mean_le_half a ha ha0
  have hm0 := coefficientMean_nonneg a ha0
  have hweights : coefficientMean (fun i => a i ^ 2) = (4 : ℝ)⁻¹ := by
    unfold coefficientMean
    rw [ha]
    norm_num
  have hvar := centeredEnergy_le_sum_sq_shift (by decide : 0 < 4)
    (fun i => a i ^ 2) (coefficientMean a ^ 2)
  have hvar' : deficit a ≤ ∑ i, (a i ^ 2 - coefficientMean a ^ 2) ^ 2 := by
    simpa only [centeredEnergy, hweights, deficit, Nat.cast_ofNat] using hvar
  calc
    _ ≤ ∑ i, (a i ^ 2 - coefficientMean a ^ 2) ^ 2 := hvar'
    _ ≤ ∑ i, (9 / 4 : ℝ) * (a i - coefficientMean a) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hai := coefficient_le_one_of_unit_nonneg a ha ha0 i
      have hsum0 : 0 ≤ a i + coefficientMean a := by linarith [ha0 i]
      have hsum : a i + coefficientMean a ≤ 3 / 2 := by linarith
      have hsq : (a i + coefficientMean a) ^ 2 ≤ 9 / 4 := by nlinarith
      calc
        _ = (a i - coefficientMean a) ^ 2 * (a i + coefficientMean a) ^ 2 := by ring
        _ ≤ _ := by simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hsq (sq_nonneg (a i - coefficientMean a))
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem four_center_shift_bounds (a : Fin 4 → ℝ) (ha : IsUnit a)
    (ha0 : ∀ i, 0 ≤ a i) (hu : centeredEnergy a ≤ 1 / 400) :
    coefficientMean a - 1 / 2 ≤ -centeredEnergy a / 4 ∧
      |coefficientMean a - 1 / 2| ≤ 13 * centeredEnergy a / 50 := by
  have hu0 := centeredEnergy_nonneg a
  have hm0 := coefficientMean_nonneg a ha0
  have hm := four_mean_le_half a ha ha0
  have hunit := centeredEnergy_add_mean_sq (by decide : 0 < 4) a
  rw [ha] at hunit
  norm_num at hunit
  have hmlo : (49 : ℝ) / 100 ≤ coefficientMean a := by nlinarith
  constructor
  · nlinarith [sq_nonneg (coefficientMean a - 1 / 2)]
  · rw [abs_of_nonpos (by linarith : coefficientMean a - 1 / 2 ≤ 0)]
    have hp := mul_nonneg (show 0 ≤ 1 / 2 - coefficientMean a by linarith)
      (show 0 ≤ coefficientMean a + 1 / 2 - 25 / 26 by linarith)
    nlinarith

theorem four_coefficient_product_le (a : Fin 4 → ℝ) (ha : IsUnit a)
    (ha0 : ∀ i, 0 ≤ a i) : ∏ i, a i ≤ 1 / 16 := by
  have h01 : a 0 * a 1 ≤ (a 0 ^ 2 + a 1 ^ 2) / 2 := by nlinarith [sq_nonneg (a 0 - a 1)]
  have h23 : a 2 * a 3 ≤ (a 2 ^ 2 + a 3 ^ 2) / 2 := by nlinarith [sq_nonneg (a 2 - a 3)]
  have hp := mul_le_mul h01 h23 (mul_nonneg (ha0 2) (ha0 3)) (by positivity)
  have hs : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 = 1 := by
    simpa only [IsUnit, Fin.sum_univ_four] using ha
  rw [Fin.prod_univ_four]
  nlinarith [sq_nonneg ((a 0 ^ 2 + a 1 ^ 2) - (a 2 ^ 2 + a 3 ^ 2))]

theorem four_shift_product (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0) (m : ℝ) :
    (∏ i, (m + z i)) = m ^ 4 - m ^ 2 * perturbationEnergy z / 2 +
      m * (∑ i, z i ^ 3) / 3 + perturbationEnergy z ^ 2 / 8 - (∑ i, z i ^ 4) / 4 := by
  have hz3 : z 3 = -z 0 - z 1 - z 2 := by
    simp only [Fin.sum_univ_four] at hz
    linarith
  simp only [Fin.prod_univ_four, Fin.sum_univ_four, perturbationEnergy, hz3]
  ring

theorem four_shift_fourth_identity (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0) (d : ℝ) :
    ∑ i, (2 * d - 2 * z i) ^ 4 = 64 * d ^ 4 + 96 * d ^ 2 * perturbationEnergy z -
      64 * d * (∑ i, z i ^ 3) + 16 * (∑ i, z i ^ 4) := by
  have hz3 : z 3 = -z 0 - z 1 - z 2 := by
    simp only [Fin.sum_univ_four] at hz
    linarith
  simp only [Fin.sum_univ_four, perturbationEnergy, hz3]
  ring

theorem four_inner_pairs_fourth_identity (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0) :
    (-2 * (z 0 + z 1)) ^ 4 + (-2 * (z 0 + z 2)) ^ 4 + (-2 * (z 0 + z 3)) ^ 4 =
      24 * perturbationEnergy z ^ 2 - 32 * (∑ i, z i ^ 4) := by
  have hz3 : z 3 = -z 0 - z 1 - z 2 := by
    simp only [Fin.sum_univ_four] at hz
    linarith
  simp only [Fin.sum_univ_four, perturbationEnergy, hz3]
  ring

end
end ENT.Small
