module

public import ENT.Small.FourGeometry
public import ENT.Small.FourLocalAlgebra
public import ENT.Small.EnclosuresFour

/-! Exact Taylor-jet algebra for the local four-dimensional numerator.
The analytic jet bounds and radial identity are explicit premises. -/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators

namespace ENT.Small
noncomputable section

theorem four_shift_sum (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0) (d : ℝ) :
    ∑ i, (2*d - 2*z i) = 8*d := by
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hz, mul_zero, sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem four_shift_sq (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0) (d : ℝ) :
    ∑ i, (2*d - 2*z i)^2 = 16*d^2 + 4*perturbationEnergy z := by
  have hz3 : z 3 = -z 0-z 1-z 2 := by simp only [Fin.sum_univ_four] at hz; linarith
  simp only [Fin.sum_univ_four, perturbationEnergy, hz3]
  ring

theorem four_shift_cube (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0) (d : ℝ) :
    ∑ i, (2*d - 2*z i)^3 = 32*d^3 + 24*d*perturbationEnergy z - 8*(∑ i, z i^3) := by
  have hz3 : z 3 = -z 0-z 1-z 2 := by simp only [Fin.sum_univ_four] at hz; linarith
  simp only [Fin.sum_univ_four, perturbationEnergy, hz3]
  ring

theorem sum_cube_abs_le_radius {n : ℕ} (z : Fin n → ℝ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hu : perturbationEnergy z = ρ^2) : |∑ i, z i^3| ≤ ρ^3 := by
  have hcoord : ∀ i, |z i| ≤ ρ := by
    intro i
    simpa only [hu, Real.sqrt_sq hρ] using abs_coordinate_le_sqrt_energy z i
  calc
    _ ≤ ∑ i, |z i^3| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ρ*z i^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_right (hcoord i) (sq_nonneg (z i))
      rw [abs_pow, show (3:ℕ)=2+1 from rfl, pow_succ, sq_abs]
      simpa only [mul_comm] using h
    _ = ρ^3 := by rw [← Finset.mul_sum]; change ρ*perturbationEnergy z = _; rw [hu]; ring

theorem four_taylor_argument_bound (z : Fin 4 → ℝ) {ρ d : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1/20) (hu : perturbationEnergy z = ρ^2)
    (hd : |d| ≤ 13*ρ^2/50) (i : Fin 4) : |2*d-2*z i| ≤ 21*ρ/10 := by
  have hzi : |z i| ≤ ρ := by
    simpa only [hu, Real.sqrt_sq hρ0] using abs_coordinate_le_sqrt_energy z i
  have hds : |d| ≤ ρ/75 := by nlinarith [mul_nonneg hρ0 (show 0 ≤ 1/20-ρ by linarith)]
  have h := abs_sub (2*d) (2*z i)
  norm_num [abs_mul] at h
  linarith

theorem four_taylor_fourth_sum_bound (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0)
    {ρ d : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1/20) (hu : perturbationEnergy z = ρ^2)
    (hd : |d| ≤ 13*ρ^2/50) : ∑ i, (2*d-2*z i)^4 ≤ 17*ρ^4 := by
  have hds : |d| ≤ ρ/75 := by nlinarith [mul_nonneg hρ0 (show 0 ≤ 1/20-ρ by linarith)]
  have hd2 := pow_le_pow_left₀ (abs_nonneg d) hds 2
  have hd4 := pow_le_pow_left₀ (abs_nonneg d) hds 4
  rw [sq_abs] at hd2
  have ha4 : |d|^4 = d^4 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, sq_abs]; ring
  rw [ha4] at hd4
  have hs3 := sum_cube_abs_le_radius z hρ0 hu
  have hs4 := sum_fourth_le_energy_sq z
  have hprod := mul_le_mul hds hs3 (abs_nonneg _) (show 0 ≤ ρ/75 by positivity)
  have hcross : -d*(∑ i, z i^3) ≤ ρ^4/75 := by
    have h := neg_le_abs (d*(∑ i, z i^3))
    rw [abs_mul] at h
    nlinarith only [h, hprod]
  have hd2u := mul_le_mul_of_nonneg_right hd2 (sq_nonneg ρ)
  rw [four_shift_fourth_identity z hz d, hu]
  rw [hu] at hs4
  nlinarith only [hd4, hd2u, hcross, hs4, pow_nonneg hρ0 4]

theorem four_taylor_fifth_remainder_bound (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0)
    {ρ d : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1/20) (hu : perturbationEnergy z = ρ^2)
    (hd : |d| ≤ 13*ρ^2/50) : (∑ i, |2*d-2*z i|^5)/30 ≤ (6/5:ℝ)*ρ^5 := by
  have hsum : (∑ i, |2*d-2*z i|^5) ≤ (21*ρ/10)*(∑ i, (2*d-2*z i)^4) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right (four_taylor_argument_bound z hρ0 hρ hu hd i)
      (show 0 ≤ (2*d-2*z i)^4 by positivity)
    have h4 : |2*d-2*z i|^4 = (2*d-2*z i)^4 := by
      rw [show (4:ℕ)=2*2 by decide, pow_mul, sq_abs]
      ring
    rw [pow_succ, h4]
    simpa only [mul_comm] using h
  have h := mul_le_mul_of_nonneg_left (four_taylor_fourth_sum_bound z hz hρ0 hρ hu hd)
    (show 0 ≤ 21*ρ/10 by positivity)
  nlinarith only [hsum, h, pow_nonneg hρ0 5]

def fourInnerJetSum (d u s₃ s₄ Fr F1r : ℝ) : ℝ :=
  4*Fr+8*d*F1r+fourJ2/2*(16*d^2+4*u)+fourJ3/6*(32*d^3+24*d*u-8*s₃)+
    fourV/24*(64*d^4+96*d^2*u-64*d*s₃+16*s₄)

def fourLocalPolynomial (d u s₃ s₄ : ℝ) : ℝ :=
  -d+(-fourH+2*fourJ2)*u+fourC*d^2-4*fourE*d*u+(4/3:ℝ)*fourE*s₃+
    fourK*d^3+4*(fourV-fourH)*d^2*u+(8/3:ℝ)*(fourH-fourV)*d*s₃+
    (8*fourH+(8/3:ℝ)*fourV)*d^4+fourH*u^2+((2/3:ℝ)*fourV-2*fourH)*s₄

theorem four_taylor_coefficient_identity (d u s₃ s₄ Fr FR F1r F1R : ℝ)
    (hc : FR-4*Fr = fourH/2) (hr : 4*fourH+8*F1r-4*F1R = -1) :
    8*((1/2+d)^4-(1/2+d)^2*u/2+(1/2+d)*s₃/3+u^2/8-s₄/4)*fourH-
      (FR+4*d*F1R+8*d^2*fourF2R)+fourInnerJetSum d u s₃ s₄ Fr F1r =
      fourLocalPolynomial d u s₃ s₄ := by
  unfold fourInnerJetSum fourLocalPolynomial fourC fourE fourK
  have h := congrArg (fun x : ℝ => d*x) hr
  nlinarith only [hc, h]

theorem four_inner_jet_sum (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0) (d Fr F1r : ℝ) :
    (∑ i, (Fr+F1r*(2*d-2*z i)+fourJ2/2*(2*d-2*z i)^2+
      fourJ3/6*(2*d-2*z i)^3+fourV/24*(2*d-2*z i)^4)) =
      fourInnerJetSum d (perturbationEnergy z) (∑ i,z i^3) (∑ i,z i^4) Fr F1r := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [four_shift_sum z hz d, four_shift_sq z hz d, four_shift_cube z hz d,
    four_shift_fourth_identity z hz d]
  unfold fourInnerJetSum
  norm_num
  ring

theorem four_taylor_numerator_lower (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0)
    (d Fr FR F1r F1R Fo G D : ℝ) (Fi : Fin 4 → ℝ)
    (hc : FR-4*Fr = fourH/2) (hr : 4*fourH+8*F1r-4*F1R = -1)
    (ho : Fo ≤ FR+4*d*F1R+8*d^2*fourF2R)
    (hi : ∀ i, Fr+F1r*(2*d-2*z i)+fourJ2/2*(2*d-2*z i)^2+
      fourJ3/6*(2*d-2*z i)^3+fourV/24*(2*d-2*z i)^4-|2*d-2*z i|^5/30 ≤ Fi i)
    (hD : D = 8*(∏ i,(1/2+d+z i))*fourH-Fo+(∑ i,Fi i)-G) :
    fourLocalPolynomial d (perturbationEnergy z) (∑ i,z i^3) (∑ i,z i^4)-G-
      (∑ i,|2*d-2*z i|^5)/30 ≤ D := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, four_inner_jet_sum z hz d Fr F1r] at hsum
  have hid := four_taylor_coefficient_identity d (perturbationEnergy z)
    (∑ i,z i^3) (∑ i,z i^4) Fr FR F1r F1R hc hr
  rw [four_shift_product z hz (1/2+d)] at hD
  linarith only [hsum, hid, ho, hD]

end
end ENT.Small
