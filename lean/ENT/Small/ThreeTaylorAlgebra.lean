module

public import ENT.Small.ThreeGeometry
public import ENT.Small.ThreeLocalAlgebra

/-! Exact extraction of the D3 polynomial from the analytic Taylor jets. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Small
noncomputable section

theorem three_shift_sum (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0) (d : ℝ) :
    ∑ i, (d - 2 * z i) = 3 * d := by
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hz, mul_zero, sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem three_shift_sq (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0) (d : ℝ) :
    ∑ i, (d - 2 * z i) ^ 2 = 3 * d ^ 2 + 4 * perturbationEnergy z := by
  have hz2 : z 2 = -z 0 - z 1 := by simp only [Fin.sum_univ_three] at hz; linarith
  simp only [Fin.sum_univ_three, perturbationEnergy, hz2]
  ring

theorem three_shift_cube (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0) (d : ℝ) :
    ∑ i, (d - 2 * z i) ^ 3 = 3 * d ^ 3 + 12 * d * perturbationEnergy z -
      24 * (z 0 * z 1 * z 2) := by
  have hz2 : z 2 = -z 0 - z 1 := by simp only [Fin.sum_univ_three] at hz; linarith
  simp only [Fin.sum_univ_three, perturbationEnergy, hz2]
  ring

theorem three_taylor_fifth_remainder_bound (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0)
    {ρ d : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 10)
    (hu : perturbationEnergy z = ρ ^ 2) (hd : |d| ≤ 3 * ρ ^ 2 / 10) :
    (∑ i, |d - 2 * z i| ^ 5) / 20 ≤ 153 * ρ ^ 5 / 200 := by
  have hsum : (∑ i, |d - 2 * z i| ^ 5) ≤
      (17 * ρ / 10) * ∑ i, (d - 2 * z i) ^ 4 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right (three_taylor_argument_bound z hz hρ0 hρ hu hd i)
      (show 0 ≤ (d - 2 * z i) ^ 4 by positivity)
    have h4 : |d - 2 * z i| ^ 4 = (d - 2 * z i) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, sq_abs]
      ring
    rw [pow_succ, h4]
    simpa only [mul_comm] using h
  apply three_taylor_error_bound z hz hρ0 hρ hu hd (by positivity) (le_refl _)
  linarith

def threeInnerJetSum (d u p Fr F1r : ℝ) : ℝ :=
  3 * Fr + 3 * d * F1r + (threeJ / 2) * (3 * d ^ 2 + 4 * u) +
    (threeV / 6) * (3 * d ^ 3 + 12 * d * u - 24 * p) +
    (Real.sqrt 3 / 24) * (3 * d ^ 4 + 24 * d ^ 2 * u - 96 * d * p + 8 * u ^ 2)

def threeLocalPolynomial (d u p : ℝ) : ℝ :=
  -4 * d / 3 + threeB * u + threeC * d ^ 2 - 2 * threeE * d * u +
    4 * threeE * p + threeK * d ^ 3 +
    Real.sqrt 3 * (u ^ 2 / 3 + d ^ 2 * u - 4 * d * p + d ^ 4 / 8)

theorem three_taylor_coefficient_identity (d u p Fr FR F1r F1R : ℝ)
    (hconstant : FR - 3 * Fr = 4 * threeR ^ 3 * threeH)
    (hradial : 12 * threeH * threeR ^ 2 + 3 * (F1r - F1R) = -4 / 3) :
    4 * ((threeR + d) ^ 3 - (threeR + d) * u / 2 + p) * threeH -
      (FR + 3 * d * F1R + (9 / 2 : ℝ) * d ^ 2 * threeF2R) +
      threeInnerJetSum d u p Fr F1r = threeLocalPolynomial d u p := by
  unfold threeInnerJetSum threeLocalPolynomial threeB threeC threeE threeK
  have hrad := congrArg (fun x : ℝ => d * x) hradial
  nlinarith only [hconstant, hrad]

theorem three_inner_jet_sum (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0)
    (d Fr F1r : ℝ) :
    (∑ i, (Fr + F1r * (d - 2 * z i) + threeJ / 2 * (d - 2 * z i) ^ 2 +
      threeV / 6 * (d - 2 * z i) ^ 3 + Real.sqrt 3 / 24 * (d - 2 * z i) ^ 4)) =
      threeInnerJetSum d (perturbationEnergy z) (z 0 * z 1 * z 2) Fr F1r := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [three_shift_sum z hz d, three_shift_sq z hz d, three_shift_cube z hz d,
    three_shift_fourth_identity z hz d]
  unfold threeInnerJetSum
  norm_num
  ring

theorem three_taylor_numerator_lower (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0)
    (d Fr FR F1r F1R Fo D : ℝ) (Fi : Fin 3 → ℝ)
    (hconstant : FR - 3 * Fr = 4 * threeR ^ 3 * threeH)
    (hradial : 12 * threeH * threeR ^ 2 + 3 * (F1r - F1R) = -4 / 3)
    (houter : Fo ≤ FR + 3 * d * F1R + (9 / 2 : ℝ) * d ^ 2 * threeF2R)
    (hinner : ∀ i, Fr + F1r * (d - 2 * z i) + threeJ / 2 * (d - 2 * z i) ^ 2 +
      threeV / 6 * (d - 2 * z i) ^ 3 + Real.sqrt 3 / 24 * (d - 2 * z i) ^ 4 -
      |d - 2 * z i| ^ 5 / 20 ≤ Fi i)
    (hD : D = 4 * ((threeR + d) ^ 3 - (threeR + d) * perturbationEnergy z / 2 +
      z 0 * z 1 * z 2) * threeH - Fo + ∑ i, Fi i) :
    threeLocalPolynomial d (perturbationEnergy z) (z 0 * z 1 * z 2) -
      (∑ i, |d - 2 * z i| ^ 5) / 20 ≤ D := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hinner i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, three_inner_jet_sum z hz d Fr F1r] at hsum
  have hid := three_taylor_coefficient_identity d (perturbationEnergy z)
    (z 0 * z 1 * z 2) Fr FR F1r F1R hconstant hradial
  linarith only [hsum, hid, houter, hD]

end
end ENT.Small
