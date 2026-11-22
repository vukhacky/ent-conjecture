module

public import ENT.Small.LocalGeometry

/-! Exact deficit expansion and a quantitative bound in the fixed-support chart. -/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace ENT.Small

noncomputable section

theorem fixedSupportCoefficients_sum_fourth {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) :
    (∑ i, fixedSupportCoefficients b i ^ 4) = (n : ℝ)⁻¹ +
      6 * (n : ℝ)⁻¹ * perturbationEnergy b +
      4 * (Real.sqrt (n : ℝ))⁻¹ * (∑ i, b i ^ 3) + ∑ i, b i ^ 4 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hr2 : ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hr4 : (n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹) ^ 4 = (n : ℝ)⁻¹ := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hr2]
    field_simp
  calc
    _ = (n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹) ^ 4 +
        4 * ((Real.sqrt (n : ℝ))⁻¹) ^ 3 * (∑ i, b i) +
        6 * ((Real.sqrt (n : ℝ))⁻¹) ^ 2 * perturbationEnergy b +
        4 * (Real.sqrt (n : ℝ))⁻¹ * (∑ i, b i ^ 3) + ∑ i, b i ^ 4 := by
      calc
        _ = ∑ i, (((Real.sqrt (n : ℝ))⁻¹) ^ 4 +
          4 * ((Real.sqrt (n : ℝ))⁻¹) ^ 3 * b i +
          6 * ((Real.sqrt (n : ℝ))⁻¹) ^ 2 * b i ^ 2 +
          4 * (Real.sqrt (n : ℝ))⁻¹ * b i ^ 3 + b i ^ 4) := by
            apply Finset.sum_congr rfl
            intro i hi
            unfold fixedSupportCoefficients diagonal
            ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, perturbationEnergy]
    _ = _ := by rw [hr4, hb, hr2]; ring

theorem deficit_normalizedPerturbation {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) :
    deficit (normalizedPerturbation b) =
      (4 * perturbationEnergy b / (n : ℝ) +
        (4 / Real.sqrt (n : ℝ)) * (∑ i, b i ^ 3) + (∑ i, b i ^ 4) -
        perturbationEnergy b ^ 2 / (n : ℝ)) / (1 + perturbationEnergy b) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hz : 0 < 1 + perturbationEnergy b := by linarith [perturbationEnergy_nonneg b]
  have hs4 : Real.sqrt (1 + perturbationEnergy b) ^ 4 = (1 + perturbationEnergy b) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hz.le]
  rw [deficit_eq_sum_pow_four_sub_inv hn (normalizedPerturbation_isUnit hn b hb)]
  unfold normalizedPerturbation
  simp_rw [div_pow, hs4]
  rw [← Finset.sum_div, fixedSupportCoefficients_sum_fourth hn b hb]
  field_simp
  ring

theorem abs_coordinate_le_sqrt_energy {n : ℕ} (b : Fin n → ℝ) (i : Fin n) :
    |b i| ≤ Real.sqrt (perturbationEnergy b) := by
  have hi : b i ^ 2 ≤ perturbationEnergy b :=
    Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa only [sq_abs, Real.sq_sqrt (perturbationEnergy_nonneg b)] using hi

theorem sum_cube_le_sqrt_energy_mul {n : ℕ} (b : Fin n → ℝ) :
    (∑ i, b i ^ 3) ≤ Real.sqrt (perturbationEnergy b) * perturbationEnergy b := by
  calc
    _ ≤ ∑ i, Real.sqrt (perturbationEnergy b) * b i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        b i ^ 3 = b i * b i ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          ((le_abs_self (b i)).trans (abs_coordinate_le_sqrt_energy b i)) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem sum_fourth_le_energy_sq {n : ℕ} (b : Fin n → ℝ) :
    (∑ i, b i ^ 4) ≤ perturbationEnergy b ^ 2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i => b i ^ 2) (fun i _ => sq_nonneg (b i))
  simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 from rfl, perturbationEnergy] using h

theorem deficit_normalizedPerturbation_le {n : ℕ} (hn : 4 ≤ n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {r : ℝ} (hr : 0 ≤ r)
    (hz : perturbationEnergy b ≤ r ^ 2) :
    deficit (normalizedPerturbation b) ≤ ((4 / (n : ℝ)) + 2 * r + r ^ 2) * perturbationEnergy b := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hs2 : 2 ≤ Real.sqrt (n : ℝ) := by nlinarith [Real.sq_sqrt hn0.le]
  have hc : 4 / Real.sqrt (n : ℝ) ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
  have hz0 := perturbationEnergy_nonneg b
  have hroot : Real.sqrt (perturbationEnergy b) ≤ r := by
    exact (Real.sqrt_le_iff).mpr ⟨hr, hz⟩
  have hcube := sum_cube_le_sqrt_energy_mul b
  have hfourth := sum_fourth_le_energy_sq b
  have hcube' : (4 / Real.sqrt (n : ℝ)) * (∑ i, b i ^ 3) ≤ 2 * r * perturbationEnergy b := by
    calc
      _ ≤ (4 / Real.sqrt (n : ℝ)) * (Real.sqrt (perturbationEnergy b) * perturbationEnergy b) :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
      _ ≤ 2 * (r * perturbationEnergy b) :=
        mul_le_mul hc (mul_le_mul_of_nonneg_right hroot hz0) (by positivity) (by norm_num)
      _ = _ := by ring
  have hfourth' : (∑ i, b i ^ 4) ≤ r ^ 2 * perturbationEnergy b :=
    hfourth.trans (by nlinarith)
  have hdef := deficit_normalizedPerturbation (by omega : 0 < n) b hb
  have hz1 : 0 < 1 + perturbationEnergy b := by linarith
  have hden : 1 ≤ (1 + perturbationEnergy b) ^ 2 := by nlinarith
  have hdef0 := deficit_nonneg (normalizedPerturbation b)
  have hid := (eq_div_iff (pow_ne_zero _ hz1.ne')).mp hdef
  have hsmall : deficit (normalizedPerturbation b) ≤
      deficit (normalizedPerturbation b) * (1 + perturbationEnergy b) ^ 2 := by
    nlinarith
  rw [hid] at hsmall
  have hdiv : 0 ≤ perturbationEnergy b ^ 2 / (n : ℝ) := by positivity
  calc
    _ ≤ 4 * perturbationEnergy b / (n : ℝ) +
        (4 / Real.sqrt (n : ℝ)) * (∑ i, b i ^ 3) + (∑ i, b i ^ 4) -
        perturbationEnergy b ^ 2 / (n : ℝ) := hsmall
    _ ≤ 4 * perturbationEnergy b / (n : ℝ) +
        2 * r * perturbationEnergy b + r ^ 2 * perturbationEnergy b := by linarith
    _ = _ := by ring

end
end ENT.Small
