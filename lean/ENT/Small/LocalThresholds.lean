module

public import ENT.Small.LocalGeometry
public import ENT.Small.EnclosuresThree

/-! Centered coefficient geometry and the n=3 local neighborhood thresholds. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Small
noncomputable section

def coefficientMean {n : ℕ} (a : Fin n → ℝ) : ℝ := (∑ i, a i) / (n : ℝ)

def centeredEnergy {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, (a i - coefficientMean a) ^ 2

theorem centeredEnergy_nonneg {n : ℕ} (a : Fin n → ℝ) : 0 ≤ centeredEnergy a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem coefficientMean_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ coefficientMean a :=
  div_nonneg (Finset.sum_nonneg fun i _ => ha i) (Nat.cast_nonneg n)

theorem sum_eq_card_mul_mean {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    ∑ i, a i = (n : ℝ) * coefficientMean a := by
  unfold coefficientMean
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp

theorem sum_centered_eq_zero {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    ∑ i, (a i - coefficientMean a) = 0 := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [sum_eq_card_mul_mean hn a, sub_self]

theorem sum_sq_centered_shift {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (c : ℝ) :
    (∑ i, (a i - c) ^ 2) = centeredEnergy a +
      (n : ℝ) * (coefficientMean a - c) ^ 2 := by
  have hzero := sum_centered_eq_zero hn a
  calc
    _ = ∑ i, ((a i - coefficientMean a) ^ 2 +
      2 * (coefficientMean a - c) * (a i - coefficientMean a) +
      (coefficientMean a - c) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = centeredEnergy a + (n : ℝ) * (coefficientMean a - c) ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, mul_zero,
        add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, centeredEnergy]

theorem centeredEnergy_add_mean_sq {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    centeredEnergy a + (n : ℝ) * coefficientMean a ^ 2 = ∑ i, a i ^ 2 := by
  simpa only [sub_zero] using (sum_sq_centered_shift hn a 0).symm

theorem centeredEnergy_le_sum_sq_shift {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (c : ℝ) : centeredEnergy a ≤ ∑ i, (a i - c) ^ 2 := by
  rw [sum_sq_centered_shift hn a c]
  exact le_add_of_nonneg_right (by positivity)

theorem coefficient_le_one_of_unit_nonneg {n : ℕ} (a : Fin n → ℝ)
    (ha : IsUnit a) (ha0 : ∀ i, 0 ≤ a i) (i : Fin n) : a i ≤ 1 := by
  have hi : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
  rw [ha] at hi
  nlinarith [ha0 i]

theorem three_mean_le_r (a : Fin 3 → ℝ) (ha : IsUnit a)
    (ha0 : ∀ i, 0 ≤ a i) : coefficientMean a ≤ threeR := by
  have h := centeredEnergy_add_mean_sq (by decide : 0 < 3) a
  rw [ha] at h
  norm_num at h
  nlinarith [centeredEnergy_nonneg a, coefficientMean_nonneg a ha0,
    threeR_sq, threeR_pos]

theorem three_small_deficit_coordinate_lower (a : Fin 3 → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (hδ : deficit a ≤ 1 / 100) (i : Fin 3) :
    (12 : ℝ) / 25 < a i ∧ 1 < a i + threeR := by
  have hi : (a i ^ 2 - (3 : ℝ)⁻¹) ^ 2 ≤ deficit a :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a j ^ 2 - (3 : ℝ)⁻¹))
      (Finset.mem_univ i)
  have habs : |a i ^ 2 - (3 : ℝ)⁻¹| ≤ 1 / 10 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 10)).mp
    rw [sq_abs]
    exact hi.trans (by norm_num at hδ ⊢; exact hδ)
  have hsq : (7 : ℝ) / 30 ≤ a i ^ 2 := by
    have h := (abs_le.mp habs).1
    norm_num at h
    linarith
  have hai : (12 : ℝ) / 25 < a i := by nlinarith [ha0 i]
  have hr : (13 : ℝ) / 25 < threeR := by nlinarith [threeR_sq, threeR_pos]
  exact ⟨hai, by linarith⟩

theorem three_centeredEnergy_le_deficit (a : Fin 3 → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (hδ : deficit a ≤ 1 / 100) :
    centeredEnergy a ≤ deficit a := by
  calc
    _ ≤ ∑ i, (a i - threeR) ^ 2 := centeredEnergy_le_sum_sq_shift (by decide) a threeR
    _ ≤ deficit a := by
      apply Finset.sum_le_sum
      intro i _
      have hi := (three_small_deficit_coordinate_lower a ha0 hδ i).2
      have hsq : 1 ≤ (a i + threeR) ^ 2 := by nlinarith
      calc
        (a i - threeR) ^ 2 ≤ (a i - threeR) ^ 2 * (a i + threeR) ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg (a i - threeR)) (show 0 ≤ (a i + threeR) ^ 2 - 1 by linarith)]
        _ = (a i ^ 2 - (3 : ℝ)⁻¹) ^ 2 := by
          calc
            _ = (a i ^ 2 - threeR ^ 2) ^ 2 := by ring
            _ = _ := by rw [threeR_sq]; norm_num

theorem three_local_radius_le (a : Fin 3 → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (hδ : deficit a ≤ 1 / 100) :
    Real.sqrt (centeredEnergy a) ≤ 1 / 10 := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by norm_num, (three_centeredEnergy_le_deficit a ha0 hδ).trans
    (by norm_num at hδ ⊢; exact hδ)⟩

theorem three_deficit_le_centeredEnergy (a : Fin 3 → ℝ) (ha : IsUnit a)
    (ha0 : ∀ i, 0 ≤ a i) : deficit a ≤ 3 * centeredEnergy a := by
  have hmean := three_mean_le_r a ha ha0
  have hm0 := coefficientMean_nonneg a ha0
  have hr : threeR ≤ 3 / 5 := by nlinarith [threeR_sq, threeR_pos]
  have hweights : coefficientMean (fun i => a i ^ 2) = (3 : ℝ)⁻¹ := by
    unfold coefficientMean
    rw [ha]
    norm_num
  have hvar := centeredEnergy_le_sum_sq_shift (by decide : 0 < 3)
    (fun i => a i ^ 2) (coefficientMean a ^ 2)
  have hvar' : deficit a ≤ ∑ i, (a i ^ 2 - coefficientMean a ^ 2) ^ 2 := by
    simpa only [centeredEnergy, hweights, deficit, Nat.cast_ofNat] using hvar
  calc
    _ ≤ ∑ i, (a i ^ 2 - coefficientMean a ^ 2) ^ 2 := hvar'
    _ ≤ ∑ i, 3 * (a i - coefficientMean a) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hai := coefficient_le_one_of_unit_nonneg a ha ha0 i
      have hsum0 : 0 ≤ a i + coefficientMean a := by linarith [ha0 i]
      have hsum : a i + coefficientMean a ≤ 8 / 5 := by linarith
      have hsq : (a i + coefficientMean a) ^ 2 ≤ 3 := by nlinarith
      calc
        _ = (a i - coefficientMean a) ^ 2 * (a i + coefficientMean a) ^ 2 := by ring
        _ ≤ _ := by simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hsq (sq_nonneg (a i - coefficientMean a))
    _ = 3 * centeredEnergy a := by rw [← Finset.mul_sum]; rfl

end
end ENT.Small
