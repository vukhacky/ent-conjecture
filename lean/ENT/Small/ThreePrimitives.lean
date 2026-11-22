module

public import ENT.Small.ThreeEntropy
public import ENT.Small.ThreePotential
public import ENT.Small.BoxFormula
public import ENT.Small.PrimitiveSmooth
public import ENT.Small.PrimitiveKernel
public import ENT.Small.TaylorFourth
public import ENT.Small.TaylorSecond
public import ENT.Small.ThreeTaylorAlgebra
public import ENT.Small.FixedSupportKL

/-! Actual n=3 primitives, Taylor bounds, and local entropy stability. -/

/-! The actual third primitive, its diagonal normalization and radial first-jet identity. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Small

noncomputable section

def threePrimitive : ℝ → ℝ := boxPrimitive (Spline.diagonalSplinePotential 3) 3

theorem integrable_threePotential : Integrable (Spline.diagonalSplinePotential 3) :=
  (integrable_log_diagonalSplineDensity 3 (by norm_num)).neg

theorem contDiff_threePrimitive_two : ContDiff ℝ 2 threePrimitive :=
  contDiff_boxPrimitive_succ (fun _ _ => integrable_threePotential.intervalIntegrable) 2

theorem contDiffOn_threePrimitive_four :
    ContDiffOn ℝ 4 threePrimitive (Ioo (-Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ))) := by
  exact contDiffOn_boxPrimitive (fun _ _ => integrable_threePotential.intervalIntegrable)
    isOpen_Ioo 1 3 contDiffOn_diagonalSplinePotential_three

theorem deriv_threePrimitive :
    deriv threePrimitive = boxPrimitive (Spline.diagonalSplinePotential 3) 2 :=
  deriv_boxPrimitive_succ_succ (fun _ _ => integrable_threePotential.intervalIntegrable) 1

theorem second_deriv_threePrimitive :
    iteratedDeriv 2 threePrimitive = boxPrimitive (Spline.diagonalSplinePotential 3) 1 :=
  iteratedDeriv_boxPrimitive_three_two (fun _ _ => integrable_threePotential.intervalIntegrable)

theorem third_deriv_threePrimitive {x : ℝ}
    (hx : x ∈ Ioo (-Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ))) :
    iteratedDeriv 3 threePrimitive x = Spline.diagonalSplinePotential 3 x :=
  iteratedDeriv_boxPrimitive_three_three (fun _ _ => integrable_threePotential.intervalIntegrable)
    isOpen_Ioo contDiffOn_diagonalSplinePotential_three.continuousOn hx

theorem fourth_deriv_threePrimitive {x : ℝ}
    (hx : x ∈ Ioo (-Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ))) :
    iteratedDeriv 4 threePrimitive x = deriv (Spline.diagonalSplinePotential 3) x :=
  iteratedDeriv_boxPrimitive_three_four (fun _ _ => integrable_threePotential.intervalIntegrable)
    isOpen_Ioo contDiffOn_diagonalSplinePotential_three.continuousOn hx

theorem threeR_mem_support :
    threeR ∈ Ioo (-Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ)) := by
  have hR : Real.sqrt (3 : ℝ) = 3 * threeR := by
    simpa only [threeR, one_div] using sqrt_three_eq_three_inv
  constructor <;> linarith [threeR_pos]

theorem threePrimitive_second_cut : iteratedDeriv 2 threePrimitive threeR = threeJ := by
  rw [second_deriv_threePrimitive]
  exact three_potential_center_integral

theorem threePrimitive_third_cut : iteratedDeriv 3 threePrimitive threeR = threeV := by
  rw [third_deriv_threePrimitive threeR_mem_support, three_potential_cut]

theorem threePrimitive_fourth_cut : iteratedDeriv 4 threePrimitive threeR = Real.sqrt (3 : ℝ) := by
  rw [fourth_deriv_threePrimitive threeR_mem_support, deriv_diagonalSplinePotential_three_cut]

theorem threePrimitive_second_right :
    iteratedDeriv 2 threePrimitive (Real.sqrt (3 : ℝ)) = threeF2R := by
  rw [second_deriv_threePrimitive]
  exact three_potential_full_integral

theorem three_expectation_primitive (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ x, Spline.diagonalSplinePotential 3 x ∂projectionLaw a) =
      (threePrimitive (a 0 + a 1 + a 2) - threePrimitive (-a 0 + a 1 + a 2) -
        threePrimitive (a 0 - a 1 + a 2) - threePrimitive (a 0 + a 1 - a 2)) /
          (4 * a 0 * a 1 * a 2) :=
  integral_projection_three_primitive a ha integrable_threePotential
    (Spline.diagonalSplinePotential_even 3 (by norm_num))

theorem three_diagonal_potential_expectation :
    (∫ x, Spline.diagonalSplinePotential 3 x ∂projectionLaw (diagonal 3)) = threeH := by
  let p := Spline.diagonalFiniteEntropyDensity 3 (by norm_num)
  calc
    _ = ∫ x, (-Real.log (p.density x)) * p.density x := p.integral_eq_density _
    _ = p.entropy := by
      unfold FiniteEntropyDensity.entropy
      rw [← integral_neg]
      congr 1
      funext x
      ring
    _ = threeH := diagonalFiniteEntropyDensity_three_entropy

theorem threePrimitive_diagonal_identity :
    threePrimitive (Real.sqrt (3 : ℝ)) - 3 * threePrimitive threeR = 4 * threeR ^ 3 * threeH := by
  have h := three_expectation_primitive (diagonal 3) (fun _ => inv_sqrt_three_pos)
  rw [three_diagonal_potential_expectation] at h
  have hd : ∀ i : Fin 3, diagonal 3 i = threeR := by
    intro i
    simp only [diagonal, Nat.cast_ofNat, threeR, one_div]
  simp only [hd] at h
  have hR : Real.sqrt (3 : ℝ) = 3 * threeR := by
    simpa only [threeR, one_div] using sqrt_three_eq_three_inv
  have hsum : threeR + threeR + threeR = Real.sqrt (3 : ℝ) := by linarith
  rw [hsum, show -threeR + threeR + threeR = threeR by ring,
    show threeR - threeR + threeR = threeR by ring,
    show threeR + threeR - threeR = threeR by ring] at h
  have hr0 := threeR_pos
  have hden : 4 * threeR * threeR * threeR ≠ 0 := by positivity
  have hm := (eq_div_iff hden).mp h
  nlinarith

theorem three_potential_outer_weighted_integral :
    (∫ x in threeR..Real.sqrt (3 : ℝ),
      (Real.sqrt (3 : ℝ) - x) * Spline.diagonalSplinePotential 3 x) =
      2 * threeR ^ 2 * (threeV + 1) := by
  have hR : Real.sqrt (3 : ℝ) = 3 * threeR := by
    simpa only [threeR, one_div] using sqrt_three_eq_three_inv
  have hrR : threeR ≤ Real.sqrt (3 : ℝ) := by linarith [threeR_pos]
  calc
    _ = ∫ x in threeR..Real.sqrt (3 : ℝ),
        (Real.sqrt (3 : ℝ) - x) * (-Real.log
          ((3 * Real.sqrt (3 : ℝ) / 16) * (Real.sqrt (3 : ℝ) - x) ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hrR] at hx
      dsimp only
      rw [three_potential_eq_outer hx]
      rfl
    _ = ∫ x in 0..2 * threeR,
        x * (-Real.log ((3 * Real.sqrt (3 : ℝ) / 16) * x ^ 2)) := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ => x * (-Real.log ((3 * Real.sqrt (3 : ℝ) / 16) * x ^ 2)))
        (a := threeR) (b := Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ))
      simpa only [sub_self, show Real.sqrt (3 : ℝ) - threeR = 2 * threeR by linarith] using h
    _ = _ := by
      rw [integral_mul_neg_log_scaled_square (by positivity)
        (mul_nonneg (by norm_num) threeR_pos.le)]
      have hcut : (3 * Real.sqrt (3 : ℝ) / 16) * (2 * threeR) ^ 2 = Real.sqrt (3 : ℝ) / 4 := by
        rw [mul_pow, threeR_sq]
        ring
      rw [hcut, threeV_eq_neg_log_cut]
      ring

theorem threePrimitive_radial_identity :
    12 * threeH * threeR ^ 2 +
      3 * (deriv threePrimitive threeR - deriv threePrimitive (Real.sqrt (3 : ℝ))) = -4 / 3 := by
  have hR : Real.sqrt (3 : ℝ) = 3 * threeR := by
    simpa only [threeR, one_div] using sqrt_three_eq_three_inv
  have hc : ContinuousOn (Spline.diagonalSplinePotential 3) (Ioo 0 (Real.sqrt (3 : ℝ))) :=
    contDiffOn_diagonalSplinePotential_three.continuousOn.mono
      (fun x hx => ⟨by linarith [hx.1, sqrt_three_pos], hx.2⟩)
  have h := boxPrimitive_two_difference
    (fun _ _ => integrable_threePotential.intervalIntegrable)
    threeR_pos.le (show threeR ≤ Real.sqrt (3 : ℝ) by linarith [threeR_pos]) hc
  rw [three_potential_center_integral, three_potential_outer_weighted_integral] at h
  rw [deriv_threePrimitive]
  have hH : threeH = 7 / 6 + threeV - 3 * threeR * Real.artanh threeR := by
    rw [threeH_eq]
    unfold threeScaledArtanh
    rw [hR]
  have hdiff : boxPrimitive (Spline.diagonalSplinePotential 3) 2 (Real.sqrt (3 : ℝ)) -
      boxPrimitive (Spline.diagonalSplinePotential 3) 2 threeR = 4 * threeH / 3 + 4 / 9 := by
    rw [h, hR, threeJ, hH]
    ring_nf
    rw [threeR_sq]
    ring
  rw [threeR_sq]
  linarith

end
end ENT.Small

/-! Taylor estimates and local entropy stability in dimension three. -/

/-! Actual analytic Taylor bounds for the local three-dimensional proof. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace ENT.Small

noncomputable section

def threeInnerTaylor (x : ℝ) : ℝ :=
  threePrimitive threeR + deriv threePrimitive threeR * (x - threeR) +
    threeJ * (x - threeR) ^ 2 / 2 + threeV * (x - threeR) ^ 3 / 6 +
      Real.sqrt (3 : ℝ) * (x - threeR) ^ 4 / 24

theorem threeInnerTaylor_eq_taylorFour (x : ℝ) :
    threeInnerTaylor x = taylorFour threePrimitive threeR x := by
  unfold threeInnerTaylor taylorFour
  rw [threePrimitive_second_cut, threePrimitive_third_cut, threePrimitive_fourth_cut]

theorem threePrimitive_inner_remainder {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (2 * threeR)) :
    |threePrimitive x - threeInnerTaylor x| ≤ |x - threeR| ^ 5 / 20 := by
  have hR : Real.sqrt (3 : ℝ) = 3 * threeR := by
    simpa only [threeR, one_div] using sqrt_three_eq_three_inv
  have hmin : 0 < min threeR x := lt_min threeR_pos hx.1
  have hmax : max threeR x < 2 * threeR := max_lt (by linarith [threeR_pos]) hx.2
  have hsub : uIcc threeR x ⊆ Ioo (-Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ)) := by
    intro y hy
    change min threeR x ≤ y ∧ y ≤ max threeR x at hy
    constructor <;> linarith [hy.1, hy.2, sqrt_three_pos]
  have hderiv : ∀ y ∈ uIoo threeR x, ∃ v : ℝ,
      HasDerivAt (iteratedDeriv 4 threePrimitive) v y ∧ |v| ≤ 6 := by
    intro y hy
    have hy0 : 0 < y := lt_trans hmin hy.1
    have hy2 : y < 2 * threeR := lt_trans hy.2 hmax
    have hyr : y ≠ threeR := by
      intro h
      subst y
      exact left_notMem_uIoo hy
    have hys : y ∈ Ioo (-Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ)) :=
      hsub ⟨hy.1.le, hy.2.le⟩
    have heq : iteratedDeriv 4 threePrimitive =ᶠ[𝓝 y] deriv (Spline.diagonalSplinePotential 3) := by
      filter_upwards [Ioo_mem_nhds hys.1 hys.2] with z hz
      exact fourth_deriv_threePrimitive hz
    rcases lt_or_gt_of_ne hyr with hyl | hyg
    · have hb := three_center_second_bound ⟨hy0.le, hyl.le⟩
      refine ⟨_, (hasDerivAt_deriv_diagonalSplinePotential_three_center
        ⟨hy0, hyl⟩).congr_of_eventuallyEq heq, ?_⟩
      rw [abs_of_nonneg hb.1]
      exact hb.2
    · have hyR : y < Real.sqrt (3 : ℝ) := by linarith [threeR_pos]
      have hb := three_outer_second_bound ⟨hyg.le, hy2.le⟩
      refine ⟨_, (hasDerivAt_deriv_diagonalSplinePotential_three_outer
        ⟨hyg, hyR⟩).congr_of_eventuallyEq heq, ?_⟩
      rw [abs_of_nonneg hb.1]
      exact hb.2
  have h := taylorFour_remainder_bound isOpen_Ioo contDiffOn_threePrimitive_four hsub hderiv
  rw [← threeInnerTaylor_eq_taylorFour] at h
  convert h using 1 <;> ring

theorem threePrimitive_inner_lower {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (2 * threeR)) :
    threeInnerTaylor x - |x - threeR| ^ 5 / 20 ≤ threePrimitive x := by
  have h := (abs_le.mp (threePrimitive_inner_remainder hx)).1
  linarith

theorem threePrimitive_outer_upper {A : ℝ} (hA0 : 0 < A) (hAR : A ≤ Real.sqrt (3 : ℝ)) :
    threePrimitive A ≤ threePrimitive (Real.sqrt (3 : ℝ)) +
      deriv threePrimitive (Real.sqrt (3 : ℝ)) * (A - Real.sqrt (3 : ℝ)) +
      threeF2R * (A - Real.sqrt (3 : ℝ)) ^ 2 / 2 := by
  rw [← threePrimitive_second_right]
  apply taylorSecond_upper_of_nonneg_third contDiff_threePrimitive_two hAR
  intro y hy
  have hys : y ∈ Ioo (-Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ)) :=
    ⟨by linarith [hy.1, sqrt_three_pos], hy.2⟩
  refine ⟨Spline.diagonalSplinePotential 3 y, ?_, (three_potential_pos hys).le⟩
  rw [second_deriv_threePrimitive]
  have hc := (contDiffOn_diagonalSplinePotential_three.continuousOn y hys).continuousAt
    (isOpen_Ioo.mem_nhds hys)
  exact hasDerivAt_intervalPrimitive (fun _ _ => integrable_threePotential.intervalIntegrable) hc
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      contDiffOn_diagonalSplinePotential_three.continuousOn y hys)

end
end ENT.Small

/-! Local stability for the actual three-dimensional projection entropy. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators

namespace ENT.Small

noncomputable section

theorem three_local_potential_gap (a : Fin 3 → ℝ) (ha : IsUnit a)
    (ha0 : ∀ i, 0 ≤ a i) (hδ : deficit a ≤ 1 / 100) :
    deficit a / 720 ≤ threeH -
      ∫ x, Spline.diagonalSplinePotential 3 x ∂projectionLaw a := by
  let m := coefficientMean a
  let z : Fin 3 → ℝ := fun i => a i - m
  let u := centeredEnergy a
  let ρ := Real.sqrt u
  let d := m - threeR
  let E := ∫ x, Spline.diagonalSplinePotential 3 x ∂projectionLaw a
  let P := a 0 * a 1 * a 2
  let D := 4 * P * (threeH - E)
  have haPos : ∀ i, 0 < a i := by
    intro i
    linarith [(three_small_deficit_coordinate_lower a ha0 hδ i).1]
  have hu0 : 0 ≤ u := centeredEnergy_nonneg a
  have hu : u = ρ ^ 2 := (Real.sq_sqrt hu0).symm
  have hz : ∑ i, z i = 0 := sum_centered_eq_zero (by decide : 0 < 3) a
  have hzu : perturbationEnergy z = u := rfl
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ : ρ ≤ 1 / 10 := three_local_radius_le a ha0 hδ
  have huSmall : u ≤ 1 / 100 := by rw [hu]; nlinarith
  have hd := three_center_shift_bounds a ha ha0 huSmall
  change d ≤ -threeR * u / 2 ∧ |d| ≤ 3 * u / 10 at hd
  have hd0 : d ≤ 0 := by nlinarith [threeR_pos]
  have hp := three_zero_sum_product_bound z hz hρ0 (hzu.trans hu)
  have hrem := three_taylor_fifth_remainder_bound z hz hρ0 hρ (hzu.trans hu)
    (by simpa only [← hu] using hd.2)
  have hR : Real.sqrt (3 : ℝ) = 3 * threeR := by
    simpa only [threeR, one_div] using sqrt_three_eq_three_inv
  have hsum : a 0 + a 1 + a 2 = 3 * m := by
    simpa only [Fin.sum_univ_three, Nat.cast_ofNat] using sum_eq_card_mul_mean (by decide : 0 < 3) a
  have hmPos : 0 < m := by
    linarith [haPos 0, haPos 1, haPos 2]
  have hA0 : 0 < Real.sqrt (3 : ℝ) + 3 * d := by dsimp [d]; linarith
  have hAR : Real.sqrt (3 : ℝ) + 3 * d ≤ Real.sqrt (3 : ℝ) := by linarith
  have houter := threePrimitive_outer_upper hA0 hAR
  have houter' : threePrimitive (Real.sqrt (3 : ℝ) + 3 * d) ≤
      threePrimitive (Real.sqrt (3 : ℝ)) + 3 * d * deriv threePrimitive (Real.sqrt (3 : ℝ)) +
        (9 / 2 : ℝ) * d ^ 2 * threeF2R := by
    convert houter using 1 <;> ring
  have hinner (i : Fin 3) : threePrimitive threeR + deriv threePrimitive threeR * (d - 2 * z i) +
      threeJ / 2 * (d - 2 * z i) ^ 2 + threeV / 6 * (d - 2 * z i) ^ 3 +
      Real.sqrt (3 : ℝ) / 24 * (d - 2 * z i) ^ 4 - |d - 2 * z i| ^ 5 / 20 ≤
        threePrimitive (threeR + (d - 2 * z i)) := by
    have hb := three_taylor_argument_bound z hz hρ0 hρ (hzu.trans hu)
      (by simpa only [← hu] using hd.2) i
    have hx : threeR + (d - 2 * z i) ∈ Ioo (0 : ℝ) (2 * threeR) := by
      have hb' := abs_le.mp hb
      constructor <;> linarith [threeR_bounds.1]
    have h := threePrimitive_inner_lower hx
    unfold threeInnerTaylor at h
    convert h using 1 <;> ring
  have hP : P = (threeR + d) ^ 3 - (threeR + d) * perturbationEnergy z / 2 + z 0 * z 1 * z 2 := by
    have h := three_shift_product z hz (threeR + d)
    have heq (i : Fin 3) : threeR + d + z i = a i := by dsimp [d, z]; ring
    simpa only [heq] using h
  have hden : 4 * a 0 * a 1 * a 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (haPos 0).ne')
      (haPos 1).ne') (haPos 2).ne'
  have hE := three_expectation_primitive a haPos
  have hargA : a 0 + a 1 + a 2 = Real.sqrt (3 : ℝ) + 3 * d := by dsimp [d]; linarith
  have harg0 : -a 0 + a 1 + a 2 = threeR + (d - 2 * z 0) := by dsimp [d, z]; linarith
  have harg1 : a 0 - a 1 + a 2 = threeR + (d - 2 * z 1) := by dsimp [d, z]; linarith
  have harg2 : a 0 + a 1 - a 2 = threeR + (d - 2 * z 2) := by dsimp [d, z]; linarith
  rw [hargA, harg0, harg1, harg2] at hE
  have hEnum := (eq_div_iff hden).mp hE
  have hD : D = 4 * ((threeR + d) ^ 3 - (threeR + d) * perturbationEnergy z / 2 +
      z 0 * z 1 * z 2) * threeH - threePrimitive (Real.sqrt (3 : ℝ) + 3 * d) +
        ∑ i, threePrimitive (threeR + (d - 2 * z i)) := by
    rw [← hP, Fin.sum_univ_three]
    dsimp [D, P, E]
    nlinarith only [hEnum]
  have hpoly := three_taylor_numerator_lower z hz d (threePrimitive threeR)
    (threePrimitive (Real.sqrt (3 : ℝ))) (deriv threePrimitive threeR)
    (deriv threePrimitive (Real.sqrt (3 : ℝ)))
    (threePrimitive (Real.sqrt (3 : ℝ) + 3 * d)) D
    (fun i => threePrimitive (threeR + (d - 2 * z i)))
    threePrimitive_diagonal_identity threePrimitive_radial_identity houter' hinner hD
  have hsc := three_scalar_bounds
  have hDlower : u / 60 ≤ D := by
    apply three_local_algebra hρ0 hρ hu threeR_pos.le sqrt_three_pos.le
      (by nlinarith [sqrt_three_sq]) hsc.1.le hsc.2.1.1.le hsc.2.2.1.1.le
      hsc.2.2.1.2.le hsc.2.2.2.2.le hd.1 hd.2 hp hrem
    simpa only [threeLocalPolynomial, hzu, ← sub_eq_add_neg] using hpoly
  have hPpos : 0 < P := mul_pos (mul_pos (haPos 0) (haPos 1)) (haPos 2)
  have hP1 : P ≤ 1 := by
    have h01 := mul_le_mul (coefficient_le_one_of_unit_nonneg a ha ha0 0)
      (coefficient_le_one_of_unit_nonneg a ha ha0 1) (ha0 1) (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at h01
    have h012 := mul_le_mul h01 (coefficient_le_one_of_unit_nonneg a ha ha0 2)
      (ha0 2) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul, P] using h012
  have hgap0 : 0 ≤ threeH - E := by
    have hD0 : 0 ≤ D := le_trans (by positivity) hDlower
    change 0 ≤ 4 * P * (threeH - E) at hD0
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4 * P)).mp hD0
  have hmul := mul_le_mul_of_nonneg_right hP1 hgap0
  have hδu := three_deficit_le_centeredEnergy a ha ha0
  change deficit a ≤ 3 * u at hδu
  change deficit a / 720 ≤ threeH - E
  dsimp [D] at hDlower
  nlinarith only [hDlower, hmul, hδu]

theorem three_local_entropy_gap (a : Fin 3 → ℝ) (ha : IsUnit a)
    (ha0 : ∀ i, 0 ≤ a i) (hδ : deficit a ≤ 1 / 100)
    (p : FiniteEntropyDensity (projectionLaw a)) :
    deficit a / 720 ≤ (Spline.diagonalFiniteEntropyDensity 3 (by norm_num)).entropy - p.entropy := by
  have hp := entropy_le_diagonal_potential_integral (by norm_num : 2 ≤ 3) a ha p
  have hg := three_local_potential_gap a ha ha0 hδ
  rw [diagonalFiniteEntropyDensity_three_entropy]
  linarith

end
end ENT.Small
