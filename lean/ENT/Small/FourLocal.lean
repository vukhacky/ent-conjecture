module

public import ENT.Small.FourAnalysis
public import ENT.Small.FourTaylorAlgebra
public import ENT.Small.FixedSupportKL

/-! Local entropy comparison in dimension four from Taylor estimates and finite scalar bounds. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace ENT.Small
noncomputable section

structure FourLocalScalarBounds : Prop where
  alpha : (11 : ℝ) / 1000 ≤ fourAlpha
  C : -(10 : ℝ) ≤ fourC
  E_nonneg : 0 ≤ fourE
  E_le : fourE ≤ (13 : ℝ) / 1000
  K : fourK ≤ 19
  H : (86 : ℝ) / 100 ≤ fourH
  V_sub_H_nonneg : 0 ≤ fourV - fourH
  V_sub_H_le : (8 : ℝ) / 3 * (fourV - fourH) ≤ 5 / 2
  quartic : -(54 : ℝ) / 100 ≤ (2 / 3 : ℝ) * fourV - 2 * fourH

def fourPairArgument (z : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun i => -2 * (z 0 + z i.succ)

theorem four_pair_argument_bound (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hu : perturbationEnergy z = ρ ^ 2) (i : Fin 3) :
    |fourPairArgument z i| ≤ 2 * ρ := by
  have hz3 : z 3 = -z 0 - z 1 - z 2 := by
    simp only [Fin.sum_univ_four] at hz
    linarith
  have hu' := hu
  simp only [perturbationEnergy, Fin.sum_univ_four, hz3] at hu'
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * ρ)).mp
  rw [sq_abs]
  fin_cases i
  · change (-2 * (z 0 + z 1)) ^ 2 ≤ (2 * ρ) ^ 2
    nlinarith only [hu', sq_nonneg (z 0 - z 1), sq_nonneg (z 0 + z 1 + 2 * z 2)]
  · change (-2 * (z 0 + z 2)) ^ 2 ≤ (2 * ρ) ^ 2
    nlinarith only [hu', sq_nonneg (z 0 - z 2), sq_nonneg (z 0 + 2 * z 1 + z 2)]
  · change (-2 * (z 0 + z 3)) ^ 2 ≤ (2 * ρ) ^ 2
    rw [hz3]
    nlinarith only [hu', sq_nonneg (z 1 - z 2), sq_nonneg (2 * z 0 + z 1 + z 2)]

theorem fourPrimitive_pair_sum_bound (z : Fin 4 → ℝ) (hz : ∑ i, z i = 0)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 20) (hu : perturbationEnergy z = ρ ^ 2) :
    (∑ i, fourPrimitive (fourPairArgument z i)) ≤
      (421 / 1000 : ℝ) * perturbationEnergy z ^ 2 := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    fourPrimitive_small_bound (le_trans (four_pair_argument_bound z hz hρ0 hu i)
      (by linarith : 2 * ρ ≤ 1 / 10)))
  have hquartic : (∑ i, (fourPairArgument z i) ^ 4) ≤ 24 * perturbationEnergy z ^ 2 := by
    have hid := four_inner_pairs_fourth_identity z hz
    have hs : 0 ≤ ∑ i : Fin 4, z i ^ 4 := Finset.sum_nonneg (fun _ _ => by positivity)
    rw [Fin.sum_univ_three]
    change (-2 * (z 0 + z 1)) ^ 4 + (-2 * (z 0 + z 2)) ^ 4 +
      (-2 * (z 0 + z 3)) ^ 4 ≤ 24 * perturbationEnergy z ^ 2
    linarith
  rw [← Finset.sum_div, ← Finset.mul_sum] at hsum
  linarith

theorem four_local_potential_gap_of_scalar_bounds (hs : FourLocalScalarBounds)
    (a : Fin 4 → ℝ) (ha : IsUnit a) (ha0 : ∀ i, 0 ≤ a i)
    (hδ : deficit a ≤ 1 / 500) :
    deficit a / 225 ≤ fourH - ∫ x, Spline.diagonalSplinePotential 4 x ∂projectionLaw a := by
  let m := coefficientMean a
  let z : Fin 4 → ℝ := fun i => a i - m
  let u := centeredEnergy a
  let ρ := Real.sqrt u
  let d := m - 1 / 2
  let E := ∫ x, Spline.diagonalSplinePotential 4 x ∂projectionLaw a
  let P := ∏ i, a i
  let D := 8 * P * (fourH - E)
  let G := ∑ i, fourPrimitive (fourPairArgument z i)
  have haPos : ∀ i, 0 < a i := by
    intro i
    linarith [(four_small_deficit_coordinate_lower a ha0 hδ i).2]
  have hu0 : 0 ≤ u := centeredEnergy_nonneg a
  have hu : u = ρ ^ 2 := (Real.sq_sqrt hu0).symm
  have hz : ∑ i, z i = 0 := sum_centered_eq_zero (by decide : 0 < 4) a
  have hzu : perturbationEnergy z = u := rfl
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ : ρ ≤ 1 / 20 := four_local_radius_le a ha0 hδ
  have huSmall : u ≤ 1 / 400 := by rw [hu]; nlinarith
  have hd := four_center_shift_bounds a ha ha0 huSmall
  change d ≤ -u / 4 ∧ |d| ≤ 13 * u / 50 at hd
  have hd0 : d ≤ 0 := by linarith
  have hsum : a 0 + a 1 + a 2 + a 3 = 4 * m := by
    simpa only [Fin.sum_univ_four, Nat.cast_ofNat] using
      sum_eq_card_mul_mean (by decide : 0 < 4) a
  have hmPos : 0 < m := by
    linarith [haPos 0, haPos 1, haPos 2, haPos 3]
  have hA0 : 0 < 2 + 4 * d := by dsimp [d]; linarith
  have hA2 : 2 + 4 * d ≤ 2 := by linarith
  have houter := fourPrimitive_outer_upper hA0 hA2
  have houter' : fourPrimitive (2 + 4 * d) ≤ fourPrimitive 2 +
      4 * d * deriv fourPrimitive 2 + 8 * d ^ 2 * fourF2R := by
    convert houter using 1 <;> ring
  have hinner (i : Fin 4) : fourPrimitive 1 + deriv fourPrimitive 1 * (2 * d - 2 * z i) +
      fourJ2 / 2 * (2 * d - 2 * z i) ^ 2 + fourJ3 / 6 * (2 * d - 2 * z i) ^ 3 +
      fourV / 24 * (2 * d - 2 * z i) ^ 4 - |2 * d - 2 * z i| ^ 5 / 30 ≤
        fourPrimitive (1 + (2 * d - 2 * z i)) := by
    have hb := four_taylor_argument_bound z hρ0 hρ (hzu.trans hu)
      (by simpa only [← hu] using hd.2) i
    have hx : 1 + (2 * d - 2 * z i) ∈ Icc ((3 : ℝ) / 4) (5 / 4) := by
      have hb' := abs_le.mp hb
      constructor <;> linarith
    have h := fourPrimitive_inner_lower hx
    unfold fourInnerTaylor at h
    convert h using 1 <;> ring
  have hpoint (i : Fin 4) : (1 / 2 : ℝ) + d + z i = a i := by dsimp [d, z]; ring
  have hden : 8 * a 0 * a 1 * a 2 * a 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (haPos 0).ne')
      (haPos 1).ne') (haPos 2).ne') (haPos 3).ne'
  have hE := (eq_div_iff hden).mp (four_expectation_primitive a haPos)
  have hargA : a 0 + a 1 + a 2 + a 3 = 2 + 4 * d := by dsimp [d]; linarith
  have harg0 : -a 0 + a 1 + a 2 + a 3 = 1 + (2 * d - 2 * z 0) := by dsimp [d, z]; linarith
  have harg1 : a 0 - a 1 + a 2 + a 3 = 1 + (2 * d - 2 * z 1) := by dsimp [d, z]; linarith
  have harg2 : a 0 + a 1 - a 2 + a 3 = 1 + (2 * d - 2 * z 2) := by dsimp [d, z]; linarith
  have harg3 : a 0 + a 1 + a 2 - a 3 = 1 + (2 * d - 2 * z 3) := by dsimp [d, z]; linarith
  have hpair0 : -a 0 - a 1 + a 2 + a 3 = fourPairArgument z 0 := by
    change -a 0 - a 1 + a 2 + a 3 = -2 * (z 0 + z 1)
    dsimp [z]
    linarith
  have hpair1 : -a 0 + a 1 - a 2 + a 3 = fourPairArgument z 1 := by
    change -a 0 + a 1 - a 2 + a 3 = -2 * (z 0 + z 2)
    dsimp [z]
    linarith
  have hpair2 : -a 0 + a 1 + a 2 - a 3 = fourPairArgument z 2 := by
    change -a 0 + a 1 + a 2 - a 3 = -2 * (z 0 + z 3)
    dsimp [z]
    linarith
  unfold fourBoxNumerator at hE
  rw [hargA, harg0, harg1, harg2, harg3, hpair0, hpair1, hpair2] at hE
  have hD : D = 8 * (∏ i, ((1 / 2 : ℝ) + d + z i)) * fourH -
      fourPrimitive (2 + 4 * d) + (∑ i, fourPrimitive (1 + (2 * d - 2 * z i))) - G := by
    simp only [hpoint, Fin.sum_univ_four]
    dsimp [D, P, E, G]
    simp only [Fin.prod_univ_four, Fin.sum_univ_three]
    nlinarith only [hE]
  have hpoly := four_taylor_numerator_lower z hz d (fourPrimitive 1) (fourPrimitive 2)
    (deriv fourPrimitive 1) (deriv fourPrimitive 2) (fourPrimitive (2 + 4 * d)) G D
    (fun i => fourPrimitive (1 + (2 * d - 2 * z i)))
    fourPrimitive_diagonal_identity fourPrimitive_radial_identity houter' hinner hD
  have hrem := four_taylor_fifth_remainder_bound z hz hρ0 hρ (hzu.trans hu)
    (by simpa only [← hu] using hd.2)
  have hG : G ≤ (421 / 1000 : ℝ) * u ^ 2 := fourPrimitive_pair_sum_bound z hz hρ0 hρ (hzu.trans hu)
  have hAlpha : (11 : ℝ) / 1000 ≤ 1 / 4 + (-fourH + 2 * fourJ2) := by
    convert hs.alpha using 1
    unfold fourAlpha
    ring
  have hDlower : u / 200 ≤ D := by
    apply four_local_algebra hρ0 hρ hu hAlpha hs.C hs.E_nonneg hs.E_le hs.K hs.H
      hs.V_sub_H_nonneg hs.V_sub_H_le hs.quartic hd.1 hd.2
      (sum_cube_abs_le_radius z hρ0 (hzu.trans hu))
      (Finset.sum_nonneg (fun _ _ => by positivity)) (sum_fourth_le_energy_sq z) hG hrem
    simpa only [fourLocalPolynomial, hzu] using hpoly
  have hPpos : 0 < P := Finset.prod_pos (fun i _ => haPos i)
  have hPbound : P ≤ 1 / 16 := four_coefficient_product_le a ha ha0
  have hgap0 : 0 ≤ fourH - E := by
    have hD0 : 0 ≤ D := le_trans (by positivity) hDlower
    change 0 ≤ 8 * P * (fourH - E) at hD0
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 8 * P)).mp hD0
  have hmul := mul_le_mul_of_nonneg_right hPbound hgap0
  have hδu := four_deficit_le_centeredEnergy a ha ha0
  change deficit a ≤ (9 / 4 : ℝ) * u at hδu
  change deficit a / 225 ≤ fourH - E
  dsimp [D] at hDlower
  nlinarith only [hDlower, hmul, hδu]

theorem four_local_entropy_gap_of_scalar_bounds (hs : FourLocalScalarBounds)
    (a : Fin 4 → ℝ) (ha : IsUnit a) (ha0 : ∀ i, 0 ≤ a i)
    (hδ : deficit a ≤ 1 / 500) (p : FiniteEntropyDensity (projectionLaw a)) :
    deficit a / 225 ≤ (Spline.diagonalFiniteEntropyDensity 4 (by norm_num)).entropy - p.entropy := by
  have hp := entropy_le_diagonal_potential_integral (by norm_num : 2 ≤ 4) a ha p
  have hg := four_local_potential_gap_of_scalar_bounds hs a ha ha0 hδ
  change deficit a / 225 ≤ fourH - p.entropy
  linarith

end
end ENT.Small
