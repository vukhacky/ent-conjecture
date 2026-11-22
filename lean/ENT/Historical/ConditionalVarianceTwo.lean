module

public import ENT.Historical.CappedVarianceTwoKernel
public import ENT.Historical.ConditionalVarianceGeneral

/-! Exact conditional second moment in dimension two, and the conditional
small-perturbation lemma in every positive dimension. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ENT.Small
noncomputable section
open Spline Historical

theorem integral_twoDifference_test (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ x, (x 0-x 1)^2 * g (sumProjection01 2 x) ∂unitCube01 2) =
      ∫ s, (unitSumSplineDensity 2 s)^3/3 * g s := by
  have h := congrArg (fun μ : Measure ℝ => ∫ s, g s ∂μ)
    twoDifferenceWeightedSumLaw_density
  rw [twoDifferenceWeightedSumLaw,
    integral_map (measurable_sumProjection01 _).aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun x : Fin 2 → ℝ => ENNReal.ofReal ((x 0-x 1)^2)) by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun s => ENNReal.ofReal ((unitSumSplineDensity 2 s)^3/3)) by
        have := continuous_unitSumSplineDensity 2; fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (unitSumSplineDensity_nonneg 2 (by omega) _) 3)
      (by norm_num : (0:ℝ) ≤ 3)), smul_eq_mul] using h

theorem twoSpline_distance_identity (s : ℝ) :
    unitSumSplineDensity 2 s * diagonalDistance 2 (sumToDiagonal 2 s)^2 =
      2 * (unitSumSplineDensity 2 s)^3 := by
  by_cases hs : s ∈ Icc (0:ℝ) 2
  · have hf : unitSumSplineDensity 2 s = min s (2-s) := by
      rw [unitSumSplineDensity_two_overlap]
      by_cases hs1 : s ≤ 1
      · rw [min_eq_right hs1, max_eq_left (by linarith : s-1 ≤ 0), sub_zero,
          max_eq_right hs.1, min_eq_left (by linarith : s ≤ 2-s)]
      · rw [min_eq_left (by linarith : 1 ≤ s), max_eq_right (by linarith : 0 ≤ s-1),
          max_eq_right (by linarith [hs.2]), min_eq_right (by linarith : 2-s ≤ s)]
        ring
    rw [hf, diagonalDistance_sumToDiagonal 2 (by omega), div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
    ring
  · rw [unitSumSplineDensity_eq_zero_of_not_mem 2 (by omega) s (by simpa using hs)]
    norm_num

theorem integral_variance_two (b : Fin 2 → ℝ) (hb : ∑ i, b i = 0)
    (f : ℝ → ℝ) (hm : Measurable f) :
    (∫ x, projection b x^2 * f (projection (diagonal 2) x) ∂cubeLaw 2) =
      perturbationEnergy b / 3 *
        ∫ x, diagonalDistance 2 (projection (diagonal 2) x)^2 *
          f (projection (diagonal 2) x) ∂cubeLaw 2 := by
  have hb1 : b 1 = - b 0 := by
    simp only [Fin.sum_univ_two] at hb
    linarith
  have hz : perturbationEnergy b = 2*(b 0)^2 := by
    simp only [perturbationEnergy, Fin.sum_univ_two, hb1]
    ring
  let G : (Fin 2 → ℝ) → ℝ := fun x => (x 0-x 1)^2 * f (sumToDiagonal 2 (sumProjection01 2 x))
  have hG : Measurable G := by
    dsimp [G]
    exact (((measurable_pi_apply 0).sub (measurable_pi_apply 1)).pow_const 2).mul
      (hm.comp ((measurable_sumToDiagonal 2).comp (measurable_sumProjection01 2)))
  have hmap : (∫ x, G (toUnitCube 2 x) ∂cubeLaw 2) = ∫ x, G x ∂unitCube01 2 := by
    rw [← cubeLaw_map_toUnitCube 2,
      integral_map (measurable_toUnitCube 2).aemeasurable hG.aestronglyMeasurable]
  have hfun : (fun x => projection b x^2 * f (projection (diagonal 2) x)) =
      (fun x => 4*(b 0)^2 * G (toUnitCube 2 x)) := by
    funext x
    rw [projection_diagonal_eq_sumToDiagonal]
    dsimp [G,projection,toUnitCube,toUnit]
    simp only [Fin.sum_univ_two,hb1]
    ring
  have hD : Measurable (fun t => diagonalDistance 2 t^2 * f t) :=
    ((continuous_diagonalDistance 2).measurable.pow_const 2).mul hm
  rw [hfun, integral_const_mul, hmap]
  change 4*(b 0)^2 * (∫ x, (x 0-x 1)^2 *
    (fun s => f (sumToDiagonal 2 s)) (sumProjection01 2 x) ∂unitCube01 2) = _
  rw [integral_twoDifference_test (fun s => f (sumToDiagonal 2 s))
      (show Measurable (fun s => f (sumToDiagonal 2 s)) from hm.comp (measurable_sumToDiagonal 2)),
    diagonal_integral_eq_sum_coordinate 2 (by omega) _ hD, hz]
  have hpoint : (fun s => unitSumSplineDensity 2 s *
      (diagonalDistance 2 (sumToDiagonal 2 s)^2 * f (sumToDiagonal 2 s))) =
      (fun s => 6 * ((unitSumSplineDensity 2 s)^3/3 * f (sumToDiagonal 2 s))) := by
    funext s
    rw [← mul_assoc, twoSpline_distance_identity]
    ring
  rw [hpoint, integral_const_mul]
  ring

theorem conditional_variance_two (b : Fin 2 → ℝ) (hb : ∑ i, b i = 0) :
    (cubeLaw 2)[(fun x => projection b x^2) | diagonalSigma 2] ≤ᵐ[cubeLaw 2]
      (fun x => perturbationEnergy b / 3 *
        diagonalDistance 2 (projection (diagonal 2) x)^2) := by
  have hT : @Measurable (Fin 2 → ℝ) ℝ (diagonalSigma 2) inferInstance
      (projection (diagonal 2)) := Measurable.of_comap_le le_rfl
  apply condExp_le_of_setIntegral_le (diagonalSigma_le 2)
    (integrable_cube_projection_sq b)
    ((integrable_cube_diagonalDistance_sq 2).const_mul _)
    ((((continuous_diagonalDistance 2).measurable.comp hT).pow_const 2).const_mul _).stronglyMeasurable
  intro s hs hfin
  obtain ⟨t, ht, rfl⟩ := hs
  have h := integral_variance_two b hb (t.indicator (fun _ : ℝ => (1:ℝ)))
    (measurable_const.indicator ht)
  rw [integral_mul_diagonal_indicator _ t ht, integral_mul_diagonal_indicator _ t ht] at h
  rw [integral_const_mul]
  exact h.le

end
end ENT.Small
