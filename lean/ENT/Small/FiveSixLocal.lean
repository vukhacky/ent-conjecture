module

public import ENT.Small.EnvelopeTransport
public import ENT.Small.VarianceBound
public import ENT.Spline.SupportInterior
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import ENT.Small.PotentialFirstMoment
public import ENT.Small.TaylorExpectation
public import ENT.Small.FixedSupportKL
public import ENT.Small.BoxPrimitive
public import ENT.Small.HessianExpectation
public import ENT.Small.LocalDeficit
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import ENT.Small.FiveSixAnalysis

@[expose] public section

/-! A measurable third-derivative bound in normalized coordinates. Its only
integrability input is the weighted unit-sum envelope specified in LocalConstants. -/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology

namespace ENT.Small
noncomputable section

def unitDiagonalDistance (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (n : ℝ) / 2) * diagonalDistance n x

def liftedLogThirdBound {n : ℕ} {γ : ℝ} (H : LogThirdEnvelope n γ) (x : ℝ) : ℝ :=
  (Real.sqrt (n : ℝ) / 2) ^ 3 * H.bound (unitDiagonalDistance n x)

theorem continuous_unitDiagonalDistance (n : ℕ) : Continuous (unitDiagonalDistance n) :=
  (continuous_diagonalDistance n).const_mul _

theorem measurable_liftedLogThirdBound {n : ℕ} {γ : ℝ} (H : LogThirdEnvelope n γ) :
    Measurable (liftedLogThirdBound H) :=
  (H.measurable.comp (continuous_unitDiagonalDistance n).measurable).const_mul _

theorem liftedLogThirdBound_nonneg {n : ℕ} {γ : ℝ} (H : LogThirdEnvelope n γ) (x : ℝ) :
    0 ≤ liftedLogThirdBound H x :=
  mul_nonneg (by positivity) (H.nonneg _)

theorem unitDiagonalDistance_eq (n : ℕ) (x : ℝ) :
    unitDiagonalDistance n x = ((n : ℝ) - Real.sqrt (n : ℝ) * |x|) / 2 := by
  unfold unitDiagonalDistance diagonalDistance
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  nlinarith only [hs]

theorem unitDiagonalDistance_sumToDiagonal (n : ℕ) (hn : 0 < n) (t : ℝ) :
    unitDiagonalDistance n (sumToDiagonal n t) = min t ((n : ℝ) - t) := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  rw [unitDiagonalDistance, diagonalDistance_sumToDiagonal n hn]
  field_simp

theorem unitDiagonalDistance_mem_half (n : ℕ) (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    unitDiagonalDistance n x ∈ Ioc (0 : ℝ) ((n : ℝ) / 2) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hxabs := abs_lt.mpr hx
  constructor
  · exact mul_pos (div_pos hs (by norm_num)) (sub_pos.mpr hxabs)
  · rw [unitDiagonalDistance_eq]
    nlinarith [mul_nonneg hs.le (abs_nonneg x)]

theorem third_deriv_diagonalPotential_neg (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    iteratedDeriv 3 (Spline.diagonalSplinePotential n) (-x) =
      -iteratedDeriv 3 (Spline.diagonalSplinePotential n) x := by
  have heq : (fun y => Spline.diagonalSplinePotential n (-y)) = Spline.diagonalSplinePotential n :=
    funext (Spline.diagonalSplinePotential_even n hn)
  have h := iteratedDeriv_comp_neg 3 (Spline.diagonalSplinePotential n) x
  rw [heq] at h
  norm_num at h
  linarith

theorem abs_third_deriv_diagonalPotential_abs (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    |iteratedDeriv 3 (Spline.diagonalSplinePotential n) (|x|)| =
      |iteratedDeriv 3 (Spline.diagonalSplinePotential n) x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, third_deriv_diagonalPotential_neg n hn, abs_neg]

theorem abs_third_deriv_diagonalPotential_eq (n : ℕ) (hn : 2 ≤ n) {x : ℝ}
    (hx : x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    |iteratedDeriv 3 (Spline.diagonalSplinePotential n) x| =
      (Real.sqrt (n : ℝ) / 2) ^ 3 * |logThirdUnitSum n (unitDiagonalDistance n x)| := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hxa : |x| ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) :=
    ⟨by linarith [abs_nonneg x], abs_lt.mpr hx⟩
  rw [← abs_third_deriv_diagonalPotential_abs n hn x,
    diagonalPotential_iteratedDeriv n hn 3 (by norm_num) hxa,
    ← unitDiagonalDistance_eq]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  change |(-(-Real.sqrt (n : ℝ) / 2) ^ 3 * logThirdUnitSum n (unitDiagonalDistance n x))| = _
  rw [show -(-Real.sqrt (n : ℝ) / 2) ^ 3 = (Real.sqrt (n : ℝ) / 2) ^ 3 by ring,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (n : ℝ) / 2) ^ 3)]

theorem liftedLogThirdBound_dominates {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (H : LogThirdEnvelope n γ) (hγ : γ < 1) {x y : ℝ}
    (hx : x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)))
    (hxy : |y - x| ≤ γ * diagonalDistance n x) :
    y ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) ∧
      |iteratedDeriv 3 (Spline.diagonalSplinePotential n) y| ≤ liftedLogThirdBound H x := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hdx : 0 < diagonalDistance n x := sub_pos.mpr (abs_lt.mpr hx)
  have habs := (abs_abs_sub_abs_le_abs_sub y x).trans hxy
  have habs' := abs_le.mp habs
  have hdy : (1 - γ) * diagonalDistance n x ≤ diagonalDistance n y ∧
      diagonalDistance n y ≤ (1 + γ) * diagonalDistance n x := by
    dsimp only [diagonalDistance] at *
    constructor <;> linarith
  have hdy0 : 0 < diagonalDistance n y :=
    lt_of_lt_of_le (mul_pos (by linarith) hdx) hdy.1
  have hy : y ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) :=
    abs_lt.mp (sub_pos.mp hdy0)
  have hxunit := unitDiagonalDistance_mem_half n (by omega) hx
  have hyunit := unitDiagonalDistance_mem_half n (by omega) hy
  have hlo := mul_le_mul_of_nonneg_left hdy.1
    (by positivity : (0 : ℝ) ≤ Real.sqrt (n : ℝ) / 2)
  have hhi := mul_le_mul_of_nonneg_left hdy.2
    (by positivity : (0 : ℝ) ≤ Real.sqrt (n : ℝ) / 2)
  have hu : unitDiagonalDistance n y ∈
      Icc ((1 - γ) * unitDiagonalDistance n x)
        (min ((n : ℝ) / 2) ((1 + γ) * unitDiagonalDistance n x)) := by
    constructor
    · unfold unitDiagonalDistance
      nlinarith only [hlo]
    · apply le_min hyunit.2
      unfold unitDiagonalDistance
      nlinarith only [hhi]
  refine ⟨hy, ?_⟩
  rw [abs_third_deriv_diagonalPotential_eq n hn hy]
  exact mul_le_mul_of_nonneg_left (H.dominates _ hxunit _ hu) (by positivity)

def foldedEnvelopeWeight {n : ℕ} {γ : ℝ} (H : LogThirdEnvelope n γ) (t : ℝ) : ℝ :=
  Spline.unitSumSplineDensity n t * (min t ((n : ℝ) - t)) ^ 3 * H.bound (min t ((n : ℝ) - t))

theorem foldedEnvelopeWeight_left {n : ℕ} {γ : ℝ} (H : LogThirdEnvelope n γ)
    {t : ℝ} (ht : t ≤ (n : ℝ) / 2) :
    foldedEnvelopeWeight H t = Spline.unitSumSplineDensity n t * t ^ 3 * H.bound t := by
  rw [foldedEnvelopeWeight, min_eq_left (by linarith)]

theorem foldedEnvelopeWeight_right {n : ℕ} (hn : 2 ≤ n) {γ : ℝ} (H : LogThirdEnvelope n γ)
    {t : ℝ} (ht : (n : ℝ) / 2 ≤ t) :
    foldedEnvelopeWeight H t = Spline.unitSumSplineDensity n ((n : ℝ) - t) *
      ((n : ℝ) - t) ^ 3 * H.bound ((n : ℝ) - t) := by
  rw [foldedEnvelopeWeight, min_eq_right (by linarith), Spline.unitSumSplineDensity_reflection n hn]

theorem foldedEnvelopeWeight_zero {n : ℕ} (hn : 2 ≤ n) {γ : ℝ} (H : LogThirdEnvelope n γ)
    {t : ℝ} (ht : t ∉ Icc (0 : ℝ) (n : ℝ)) : foldedEnvelopeWeight H t = 0 := by
  rw [foldedEnvelopeWeight, Spline.unitSumSplineDensity_eq_zero_of_not_mem n hn t ht,
    zero_mul, zero_mul]

theorem intervalIntegrable_foldedEnvelopeWeight_left {n : ℕ} {γ : ℝ} (H : LogThirdEnvelope n γ) :
    IntervalIntegrable (foldedEnvelopeWeight H) volume 0 ((n : ℝ) / 2) := by
  apply H.weighted_integrable.congr_uIoo
  intro t ht
  rw [uIoo_of_le (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)] at ht
  exact (foldedEnvelopeWeight_left H ht.2.le).symm

theorem intervalIntegrable_foldedEnvelopeWeight_right {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (H : LogThirdEnvelope n γ) :
    IntervalIntegrable (foldedEnvelopeWeight H) volume ((n : ℝ) / 2) (n : ℝ) := by
  have hr : IntervalIntegrable
      (fun t => Spline.unitSumSplineDensity n ((n : ℝ) - t) * ((n : ℝ) - t) ^ 3 *
        H.bound ((n : ℝ) - t)) volume ((n : ℝ) / 2) (n : ℝ) := by
    simpa only [sub_zero, show (n : ℝ) - (n : ℝ) / 2 = (n : ℝ) / 2 by ring] using
      (H.weighted_integrable.comp_sub_left (n : ℝ)).symm
  apply hr.congr_uIoo
  intro t ht
  rw [uIoo_of_le (by nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n] :
    (n : ℝ) / 2 ≤ (n : ℝ))] at ht
  exact (foldedEnvelopeWeight_right hn H ht.1.le).symm

theorem integrable_foldedEnvelopeWeight {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (H : LogThirdEnvelope n γ) : Integrable (foldedEnvelopeWeight H) volume := by
  have hfull := (intervalIntegrable_foldedEnvelopeWeight_left H).trans
    (intervalIntegrable_foldedEnvelopeWeight_right hn H)
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le (Nat.cast_nonneg n)).mp hfull
  exact hi.integrable_of_forall_notMem_eq_zero (fun _ ht => foldedEnvelopeWeight_zero hn H ht)

theorem integral_foldedEnvelopeWeight {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (H : LogThirdEnvelope n γ) :
    (∫ t, foldedEnvelopeWeight H t) = averagedRemainderBound n H.bound := by
  have hsupport := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (fun t ht => foldedEnvelopeWeight_zero hn H ht)
  rw [← hsupport, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_foldedEnvelopeWeight_left H) (intervalIntegrable_foldedEnvelopeWeight_right hn H)]
  have hl : (∫ t in 0..((n : ℝ) / 2), foldedEnvelopeWeight H t) =
      ∫ t in 0..((n : ℝ) / 2), Spline.unitSumSplineDensity n t * t ^ 3 * H.bound t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)] at ht
    exact foldedEnvelopeWeight_left H ht.2
  have hr : (∫ t in ((n : ℝ) / 2)..(n : ℝ), foldedEnvelopeWeight H t) =
      ∫ t in 0..((n : ℝ) / 2), Spline.unitSumSplineDensity n t * t ^ 3 * H.bound t := by
    calc
      _ = ∫ t in ((n : ℝ) / 2)..(n : ℝ),
          Spline.unitSumSplineDensity n ((n : ℝ) - t) * ((n : ℝ) - t) ^ 3 * H.bound ((n : ℝ) - t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n] :
          (n : ℝ) / 2 ≤ (n : ℝ))] at ht
        exact foldedEnvelopeWeight_right hn H ht.1
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left
          (f := fun t => Spline.unitSumSplineDensity n t * t ^ 3 * H.bound t)
          (a := (n : ℝ) / 2) (b := (n : ℝ)) (n : ℝ)]
        simp only [sub_self, show (n : ℝ) - (n : ℝ) / 2 = (n : ℝ) / 2 by ring]
  rw [hl, hr]
  unfold averagedRemainderBound
  ring

theorem liftedEnvelope_weighted_sum_coordinate {n : ℕ} (hn : 0 < n) {γ : ℝ}
    (H : LogThirdEnvelope n γ) (t : ℝ) :
    Spline.unitSumSplineDensity n t *
      (diagonalDistance n (sumToDiagonal n t) ^ 3 * liftedLogThirdBound H (sumToDiagonal n t)) =
        foldedEnvelopeWeight H t := by
  unfold liftedLogThirdBound
  rw [unitDiagonalDistance_sumToDiagonal n hn]
  have hc := unitDiagonalDistance_sumToDiagonal n hn t
  unfold unitDiagonalDistance at hc
  unfold foldedEnvelopeWeight
  rw [← hc]
  ring

theorem integrable_distance_cube_liftedEnvelope {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (H : LogThirdEnvelope n γ) :
    Integrable (fun x => diagonalDistance n (projection (diagonal n) x) ^ 3 *
      liftedLogThirdBound H (projection (diagonal n) x)) (cubeLaw n) := by
  apply (integrable_diagonal_iff_sum_coordinate n hn
    (fun x => diagonalDistance n x ^ 3 * liftedLogThirdBound H x)
    (((continuous_diagonalDistance n).measurable.pow_const 3).mul (measurable_liftedLogThirdBound H))).mpr
  simp_rw [liftedEnvelope_weighted_sum_coordinate (by omega) H]
  exact integrable_foldedEnvelopeWeight hn H

theorem integral_distance_cube_liftedEnvelope {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (H : LogThirdEnvelope n γ) :
    (∫ x, diagonalDistance n (projection (diagonal n) x) ^ 3 *
      liftedLogThirdBound H (projection (diagonal n) x) ∂cubeLaw n) =
        averagedRemainderBound n H.bound := by
  rw [diagonal_integral_eq_sum_coordinate n hn
    (fun x => diagonalDistance n x ^ 3 * liftedLogThirdBound H x)
    (((continuous_diagonalDistance n).measurable.pow_const 3).mul (measurable_liftedLogThirdBound H))]
  simp_rw [liftedEnvelope_weighted_sum_coordinate (by omega) H]
  exact integral_foldedEnvelopeWeight hn H

end
end ENT.Small

/-! Actual expected Taylor remainder under the cube law. The variance
comparison receives a nonnegative clipped test and only its distance-squared
weighted integrability; no integrability of the envelope alone is assumed. -/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ENT.Small
noncomputable section

theorem cube_diagonal_mem_support {n : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ x ∂cubeLaw n, projection (diagonal n) x ∈
      Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := by
  exact ae_of_ae_map (measurable_projection (diagonal n)).aemeasurable
    (Spline.ae_mem_diagonalSplineSupport n hn)

theorem integrable_fixedSupport_potential_increment {n : ℕ} (hn : 2 ≤ n)
    (b : Fin n → ℝ) {γ : ℝ} (hγ : γ < 1)
    (hbound : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ) :
    Integrable (fun x => Spline.diagonalSplinePotential n
      (projection (diagonal n) x + projection b x) -
        Spline.diagonalSplinePotential n (projection (diagonal n) x)) (cubeLaw n) := by
  have hm : Measurable (Spline.diagonalSplinePotential n) :=
    (Spline.continuous_diagonalSplineDensity n).measurable.log.neg
  have hzero : Integrable (fun x => Spline.diagonalSplinePotential n (projection (diagonal n) x))
      (cubeLaw n) := by
    have hi := integrable_self_potential (Spline.diagonalFiniteEntropyDensity n hn)
    exact (integrable_map_measure (μ := cubeLaw n) hm.aestronglyMeasurable
      (measurable_projection (diagonal n)).aemeasurable).mp hi
  have hshift : Integrable (fun x => Spline.diagonalSplinePotential n
      (projection (fixedSupportCoefficients b) x)) (cubeLaw n) := by
    cases n with
    | zero => omega
    | succ m =>
        have hpos := fixedSupportCoefficients_pos (by omega : 0 < m + 1) b hγ hbound
        have hi := integrable_projection_of_integrable (fixedSupportCoefficients b) 0 (hpos 0)
          (integrable_log_diagonalSplineDensity (m + 1) hn).neg
        exact (integrable_map_measure (μ := cubeLaw (m + 1)) hm.aestronglyMeasurable
          (measurable_projection (fixedSupportCoefficients b)).aemeasurable).mp hi
  simpa only [projection_fixedSupport] using hshift.sub' hzero

def nonnegativeEnvelopeTest {n : ℕ} {γ : ℝ} (H : LogThirdEnvelope n γ) (x : ℝ) : ℝ :=
  max 0 (diagonalDistance n x) * liftedLogThirdBound H x

theorem nonnegativeEnvelopeTest_measurable {n : ℕ} {γ : ℝ} (H : LogThirdEnvelope n γ) :
    Measurable (nonnegativeEnvelopeTest H) :=
  (measurable_const.max (continuous_diagonalDistance n).measurable).mul
    (measurable_liftedLogThirdBound H)

theorem nonnegativeEnvelopeTest_nonneg {n : ℕ} {γ : ℝ} (H : LogThirdEnvelope n γ) (x : ℝ) :
    0 ≤ nonnegativeEnvelopeTest H x :=
  mul_nonneg (le_max_left _ _) (liftedLogThirdBound_nonneg H x)

theorem envelope_test_weight_ae {n : ℕ} (hn : 2 ≤ n) {γ : ℝ} (H : LogThirdEnvelope n γ) :
    (fun x => diagonalDistance n (projection (diagonal n) x) ^ 2 *
      nonnegativeEnvelopeTest H (projection (diagonal n) x)) =ᵐ[cubeLaw n]
        (fun x => diagonalDistance n (projection (diagonal n) x) ^ 3 *
          liftedLogThirdBound H (projection (diagonal n) x)) := by
  filter_upwards [cube_diagonal_mem_support hn] with x hx
  have hd : 0 ≤ diagonalDistance n (projection (diagonal n) x) :=
    (sub_pos.mpr (abs_lt.mpr hx)).le
  dsimp only [nonnegativeEnvelopeTest]
  rw [max_eq_right hd]
  ring

theorem integrable_envelope_test_weight {n : ℕ} (hn : 2 ≤ n) {γ : ℝ} (H : LogThirdEnvelope n γ) :
    Integrable (fun x => diagonalDistance n (projection (diagonal n) x) ^ 2 *
      nonnegativeEnvelopeTest H (projection (diagonal n) x)) (cubeLaw n) :=
  (integrable_distance_cube_liftedEnvelope hn H).congr (envelope_test_weight_ae hn H).symm

theorem integrable_envelope_remainder {n : ℕ} (hn : 2 ≤ n) (b : Fin n → ℝ)
    (hb : ∑ i, b i = 0) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hbound : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ) (H : LogThirdEnvelope n γ) :
    Integrable (fun x => liftedLogThirdBound H (projection (diagonal n) x) * |projection b x| ^ 3)
      (cubeLaw n) := by
  apply ((integrable_distance_cube_liftedEnvelope hn H).const_mul (γ ^ 3)).mono'
    (((measurable_liftedLogThirdBound H).comp (measurable_projection (diagonal n))).mul
      ((continuous_abs.measurable.comp (measurable_projection b)).pow_const 3)).aestronglyMeasurable
  filter_upwards [cubeLaw_ae_mem n, cube_diagonal_mem_support hn] with x hx hT
  have hd : 0 ≤ diagonalDistance n (projection (diagonal n) x) := (sub_pos.mpr (abs_lt.mpr hT)).le
  have hy := projection_zero_sum_support_distance (by omega) b x hb hx hbound
  change |projection b x| ≤ γ * diagonalDistance n (projection (diagonal n) x) at hy
  have hp := pow_le_pow_left₀ (abs_nonneg _) hy 3
  have hh := liftedLogThirdBound_nonneg H (projection (diagonal n) x)
  have hm := mul_le_mul_of_nonneg_left hp hh
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh (pow_nonneg (abs_nonneg _) 3))]
  nlinarith only [hm]

theorem integrable_projection_sq_envelope_test {n : ℕ} (hn : 2 ≤ n) (b : Fin n → ℝ)
    (hb : ∑ i, b i = 0) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hbound : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ) (H : LogThirdEnvelope n γ) :
    Integrable (fun x => projection b x ^ 2 * nonnegativeEnvelopeTest H (projection (diagonal n) x))
      (cubeLaw n) := by
  apply ((integrable_distance_cube_liftedEnvelope hn H).const_mul (γ ^ 2)).mono'
    (((measurable_projection b).pow_const 2).mul
      ((nonnegativeEnvelopeTest_measurable H).comp (measurable_projection (diagonal n)))).aestronglyMeasurable
  filter_upwards [cubeLaw_ae_mem n, cube_diagonal_mem_support hn] with x hx hT
  have hd : 0 ≤ diagonalDistance n (projection (diagonal n) x) := (sub_pos.mpr (abs_lt.mpr hT)).le
  have hy := projection_zero_sum_support_distance (by omega) b x hb hx hbound
  change |projection b x| ≤ γ * diagonalDistance n (projection (diagonal n) x) at hy
  have hp := pow_le_pow_left₀ (abs_nonneg _) hy 2
  rw [sq_abs] at hp
  have hh := liftedLogThirdBound_nonneg H (projection (diagonal n) x)
  have hm := mul_le_mul_of_nonneg_right hp (mul_nonneg hd hh)
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (nonnegativeEnvelopeTest_nonneg H _))]
  dsimp only [nonnegativeEnvelopeTest]
  rw [max_eq_right hd]
  nlinarith only [hm]

theorem integral_envelope_remainder_le {n : ℕ} (hn : n = 5 ∨ n = 6)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hbound : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ) (H : LogThirdEnvelope n γ) :
    (∫ x, liftedLogThirdBound H (projection (diagonal n) x) * |projection b x| ^ 3 ∂cubeLaw n) ≤
      γ * perturbationEnergy b / ((n : ℝ) + 1) * averagedRemainderBound n H.bound := by
  have hn2 : 2 ≤ n := by omega
  have hR := integrable_envelope_remainder hn2 b hb hγ0 hbound H
  have hS := integrable_projection_sq_envelope_test hn2 b hb hγ0 hbound H
  have hpoint : ∀ᵐ x ∂cubeLaw n,
      liftedLogThirdBound H (projection (diagonal n) x) * |projection b x| ^ 3 ≤
        γ * (projection b x ^ 2 * nonnegativeEnvelopeTest H (projection (diagonal n) x)) := by
    filter_upwards [cubeLaw_ae_mem n, cube_diagonal_mem_support hn2] with x hx hT
    have hd : 0 ≤ diagonalDistance n (projection (diagonal n) x) := (sub_pos.mpr (abs_lt.mpr hT)).le
    have hy := projection_zero_sum_support_distance (by omega) b x hb hx hbound
    change |projection b x| ≤ γ * diagonalDistance n (projection (diagonal n) x) at hy
    have hm := mul_le_mul_of_nonneg_right hy
      (mul_nonneg (sq_nonneg (projection b x))
        (liftedLogThirdBound_nonneg H (projection (diagonal n) x)))
    rw [nonnegativeEnvelopeTest, max_eq_right hd,
      show |projection b x| ^ 3 = projection b x ^ 2 * |projection b x| by
        rw [pow_succ, sq_abs]]
    nlinarith only [hm]
  have hRS := integral_mono_ae hR (hS.const_mul γ) hpoint
  rw [integral_const_mul] at hRS
  have hvar := (integral_variance_bound_nonnegative_test hn b hb (nonnegativeEnvelopeTest H)
    (nonnegativeEnvelopeTest_measurable H) (nonnegativeEnvelopeTest_nonneg H)
    (integrable_envelope_test_weight hn2 H)).2
  rw [integral_congr_ae (envelope_test_weight_ae hn2 H),
    integral_distance_cube_liftedEnvelope hn2 H] at hvar
  have hm := mul_le_mul_of_nonneg_left hvar hγ0
  calc
    _ ≤ γ * (∫ x, projection b x ^ 2 * nonnegativeEnvelopeTest H
        (projection (diagonal n) x) ∂cubeLaw n) := hRS
    _ ≤ γ * (perturbationEnergy b / ((n : ℝ) + 1) *
        averagedRemainderBound n H.bound) := hm
    _ = _ := by ring

end
end ENT.Small

/-! Actual local entropy comparison in dimensions five and six. The
analytic estimate uses a proved measurable third-derivative envelope and
the genuine Hessian expectation. No conditional law or integrability of
the unweighted envelope is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 700000
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ENT.Small
noncomputable section

theorem fixedSupport_segment_envelope {n : ℕ} (hn : 2 ≤ n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {γ : ℝ} (hγ : γ < 1)
    (hbound : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ) (H : LogThirdEnvelope n γ) :
    ∀ᵐ ω ∂cubeLaw n, ∀ x ∈ uIcc (projection (diagonal n) ω)
      (projection (diagonal n) ω + projection b ω),
      x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) ∧
        |iteratedDeriv 3 (Spline.diagonalSplinePotential n) x| ≤
          liftedLogThirdBound H (projection (diagonal n) ω) := by
  filter_upwards [cubeLaw_ae_mem n, cube_diagonal_mem_support hn] with ω hω hT
  intro x hx
  have hy := projection_zero_sum_support_distance (by omega) b ω hb hω hbound
  have hx' := abs_sub_left_of_mem_uIcc hx
  simp only [add_sub_cancel_left] at hx'
  exact liftedLogThirdBound_dominates hn H hγ hT (hx'.trans hy)

theorem diagonalPotential_hasDerivAt_second {n : ℕ} (hn : 5 ≤ n) {x : ℝ}
    (hx : x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    HasDerivAt (iteratedDeriv 2 (Spline.diagonalSplinePotential n))
      (iteratedDeriv 3 (Spline.diagonalSplinePotential n) x) x := by
  have h3 := (Spline.diagonalSplinePotential_contDiffOn 3 n (by omega)).contDiffAt
    (isOpen_Ioo.mem_nhds hx)
  have h2 : ContDiffAt ℝ 2 (deriv (Spline.diagonalSplinePotential n)) x :=
    h3.derivWithin (by norm_num)
  have h1 : ContDiffAt ℝ 1 (deriv (deriv (Spline.diagonalSplinePotential n))) x :=
    h2.derivWithin (by norm_num)
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    (h1.differentiableAt (by norm_num)).hasDerivAt

theorem integral_fixedSupport_potential_increment_le {n : ℕ} (hn : n = 5 ∨ n = 6)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1)
    (hbound : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ) (H : LogThirdEnvelope n γ) :
    (∫ x, Spline.diagonalSplinePotential n
        (projection (diagonal n) x + projection b x) -
      Spline.diagonalSplinePotential n (projection (diagonal n) x) ∂cubeLaw n) ≤
      (1 - smallKappa n) * perturbationEnergy b / 2 +
        γ * perturbationEnergy b / ((n : ℝ) + 1) * averagedRemainderBound n H.bound / 6 := by
  have hn2 : 2 ≤ n := by omega
  have hsegment := fixedSupport_segment_envelope hn2 b hb hγ hbound H
  have hsub : ∀ᵐ ω ∂cubeLaw n,
      uIcc (projection (diagonal n) ω) (projection (diagonal n) ω + projection b ω) ⊆
        Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) :=
    hsegment.mono fun ω hω x hx => (hω x hx).1
  have hd : ∀ᵐ ω ∂cubeLaw n, ∀ x ∈ uIoo (projection (diagonal n) ω)
      (projection (diagonal n) ω + projection b ω), ∃ v : ℝ,
        HasDerivAt (iteratedDeriv 2 (Spline.diagonalSplinePotential n)) v x ∧
          |v| ≤ liftedLogThirdBound H (projection (diagonal n) ω) := by
    filter_upwards [hsegment] with ω hω
    intro x hx
    have hx' := hω x ⟨hx.1.le, hx.2.le⟩
    exact ⟨_, diagonalPotential_hasDerivAt_second (by omega) hx'.1, hx'.2⟩
  obtain ⟨hquad', hquadval'⟩ := hessian_expectation_five_six hn b hb
  have hquad : Integrable (fun x => iteratedDeriv 2 (Spline.diagonalSplinePotential n)
      (projection (diagonal n) x) * projection b x ^ 2) (cubeLaw n) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, mul_comm] using hquad'
  have hquadval : (∫ x, iteratedDeriv 2 (Spline.diagonalSplinePotential n)
      (projection (diagonal n) x) * projection b x ^ 2 ∂cubeLaw n) =
        (1 - smallKappa n) * perturbationEnergy b := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, mul_comm] using hquadval'
  have htaylor := integral_taylorTwo_increment_upper (cubeLaw n)
    (projection (diagonal n)) (projection b)
    (fun x => liftedLogThirdBound H (projection (diagonal n) x))
    (Spline.diagonalSplinePotential n) isOpen_Ioo
    (Spline.diagonalSplinePotential_contDiffOn 2 n (by omega)) hsub hd
    (integrable_fixedSupport_potential_increment hn2 b hγ hbound)
    (integrable_linear_potential_term (by omega) b) hquad
    (integrable_envelope_remainder hn2 b hb hγ0 hbound H)
  rw [integral_linear_potential_term (by omega) b hb, zero_add, hquadval] at htaylor
  have hrem := integral_envelope_remainder_le hn b hb hγ0 hbound H
  linarith

theorem log_one_add_quadratic_lower {z : ℝ} (hz : 0 ≤ z) :
    z - z ^ 2 / 2 ≤ Real.log (1 + z) := by
  apply le_trans ?_ (Real.le_log_one_add_of_nonneg hz)
  apply (le_div_iff₀ (by linarith : 0 < z + 2)).mpr
  nlinarith [mul_nonneg hz (sq_nonneg z)]

theorem five_six_local_entropy_upper {n : ℕ} (hn : n = 5 ∨ n = 6)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1)
    (hbound : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ) (H : LogThirdEnvelope n γ)
    (p : FiniteEntropyDensity (projectionLaw (normalizedPerturbation b))) :
    p.entropy - (Spline.diagonalFiniteEntropyDensity n (by omega)).entropy ≤
      perturbationEnergy b * (-smallKappa n / 2 + perturbationEnergy b / 4 +
        γ * averagedRemainderBound n H.bound / (6 * ((n : ℝ) + 1))) := by
  have hKL := entropy_fixedSupport_cube (by omega) b hb hγ hbound p
  have hinc := integral_fixedSupport_potential_increment_le hn b hb hγ0 hγ hbound H
  have hlog := log_one_add_quadratic_lower (perturbationEnergy_nonneg b)
  have heq : (1 - smallKappa n) * perturbationEnergy b / 2 +
      γ * perturbationEnergy b / ((n : ℝ) + 1) * averagedRemainderBound n H.bound / 6 -
        (perturbationEnergy b - perturbationEnergy b ^ 2 / 2) / 2 =
      perturbationEnergy b * (-smallKappa n / 2 + perturbationEnergy b / 4 +
        γ * averagedRemainderBound n H.bound / (6 * ((n : ℝ) + 1))) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  linarith only [hKL, hinc, hlog, heq]

end
end ENT.Small

/-! Local stability from a lower bound for κ and a weighted remainder bound. -/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace ENT.Small
noncomputable section

theorem five_perturbation_coordinate_bound (b : Fin 5 → ℝ) (hb : ∑ i, b i = 0)
    (hz : perturbationEnergy b ≤ (29 / 1000 : ℝ) ^ 2) (i : Fin 5) :
    Real.sqrt (5 : ℝ) * |b i| ≤ 29 / 500 := by
  have hi := zero_sum_coordinate_sq_bound b hb i
  apply (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 29 / 500)).mp
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), sq_abs]
  norm_num at hi
  nlinarith

theorem six_perturbation_coordinate_bound (b : Fin 6 → ℝ) (hb : ∑ i, b i = 0)
    (hz : perturbationEnergy b ≤ (7 / 400 : ℝ) ^ 2) (i : Fin 6) :
    Real.sqrt (6 : ℝ) * |b i| ≤ 1 / 25 := by
  have hi := zero_sum_coordinate_sq_bound b hb i
  apply (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 25)).mp
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), sq_abs]
  norm_num at hi
  nlinarith

theorem five_normalized_local_entropy_gap (H : LogThirdEnvelope 5 (29 / 500))
    (hM : averagedRemainderBound 5 H.bound ≤ 77 / 10)
    (hκ : 27 / 1000 ≤ smallKappa 5)
    (b : Fin 5 → ℝ) (hb : ∑ i, b i = 0)
    (hz : perturbationEnergy b ≤ (29 / 1000 : ℝ) ^ 2)
    (p : FiniteEntropyDensity (projectionLaw (normalizedPerturbation b))) :
    deficit (normalizedPerturbation b) / 1000 ≤
      (Spline.diagonalFiniteEntropyDensity 5 (by decide)).entropy - p.entropy := by
  have h := five_six_local_entropy_upper (Or.inl rfl) b hb (by norm_num : (0 : ℝ) ≤ 29 / 500)
    (by norm_num : (29 / 500 : ℝ) < 1) (five_perturbation_coordinate_bound b hb hz) H p
  have hδ := deficit_normalizedPerturbation_le (by decide : 4 ≤ 5) b hb
    (by norm_num : (0 : ℝ) ≤ 29 / 1000) hz
  have hmargin : -smallKappa 5 / 2 + perturbationEnergy b / 4 +
      (29 / 500 : ℝ) * averagedRemainderBound 5 H.bound / (6 * ((5 : ℝ) + 1)) ≤
      -((4 / (5 : ℝ)) + 2 * (29 / 1000) + (29 / 1000) ^ 2) / 1000 := by
    linarith only [hκ, hM, hz]
  have hm := mul_le_mul_of_nonneg_left hmargin (perturbationEnergy_nonneg b)
  norm_num only [Nat.cast_ofNat] at h hδ
  linarith only [h, hδ, hm]

theorem six_normalized_local_entropy_gap (H : LogThirdEnvelope 6 (1 / 25))
    (hM : averagedRemainderBound 6 H.bound ≤ 13 / 2)
    (hκ : 17 / 1000 ≤ smallKappa 6)
    (b : Fin 6 → ℝ) (hb : ∑ i, b i = 0)
    (hz : perturbationEnergy b ≤ (7 / 400 : ℝ) ^ 2)
    (p : FiniteEntropyDensity (projectionLaw (normalizedPerturbation b))) :
    deficit (normalizedPerturbation b) / 1000 ≤
      (Spline.diagonalFiniteEntropyDensity 6 (by decide)).entropy - p.entropy := by
  have h := five_six_local_entropy_upper (Or.inr rfl) b hb (by norm_num : (0 : ℝ) ≤ 1 / 25)
    (by norm_num : (1 / 25 : ℝ) < 1) (six_perturbation_coordinate_bound b hb hz) H p
  have hδ := deficit_normalizedPerturbation_le (by decide : 4 ≤ 6) b hb
    (by norm_num : (0 : ℝ) ≤ 7 / 400) hz
  have hmargin : -smallKappa 6 / 2 + perturbationEnergy b / 4 +
      (1 / 25 : ℝ) * averagedRemainderBound 6 H.bound / (6 * ((6 : ℝ) + 1)) ≤
      -((4 / (6 : ℝ)) + 2 * (7 / 400) + (7 / 400) ^ 2) / 1000 := by
    linarith only [hκ, hM, hz]
  have hm := mul_le_mul_of_nonneg_left hmargin (perturbationEnergy_nonneg b)
  norm_num only [Nat.cast_ofNat] at h hδ
  linarith only [h, hδ, hm]

theorem five_local_entropy_gap_of_enclosures (H : LogThirdEnvelope 5 (29 / 500))
    (hM : averagedRemainderBound 5 H.bound ≤ 77 / 10)
    (hκ : 27 / 1000 ≤ smallKappa 5)
    (a : Fin 5 → ℝ) (ha : IsUnit a) (ha0 : ∀ i, 0 ≤ a i)
    (hδ : deficit a ≤ 7 / 12500) (p : FiniteEntropyDensity (projectionLaw a)) :
    deficit a / 1000 ≤ (Spline.diagonalFiniteEntropyDensity 5 (by decide)).entropy - p.entropy := by
  obtain ⟨hb, heq, hz⟩ := five_centeredChart_local a ha ha0 hδ
  let p' := p.transport (congrArg projectionLaw heq.symm)
  have h := five_normalized_local_entropy_gap H hM hκ (centeredChart a) hb hz p'
  simpa only [p', FiniteEntropyDensity.entropy_transport, heq] using h

theorem six_local_entropy_gap_of_enclosures (H : LogThirdEnvelope 6 (1 / 25))
    (hM : averagedRemainderBound 6 H.bound ≤ 13 / 2)
    (hκ : 17 / 1000 ≤ smallKappa 6)
    (a : Fin 6 → ℝ) (ha : IsUnit a) (ha0 : ∀ i, 0 ≤ a i)
    (hδ : deficit a ≤ 1 / 6000) (p : FiniteEntropyDensity (projectionLaw a)) :
    deficit a / 1000 ≤ (Spline.diagonalFiniteEntropyDensity 6 (by decide)).entropy - p.entropy := by
  obtain ⟨hb, heq, hz⟩ := six_centeredChart_local a ha ha0 hδ
  let p' := p.transport (congrArg projectionLaw heq.symm)
  have h := six_normalized_local_entropy_gap H hM hκ (centeredChart a) hb hz p'
  simpa only [p', FiniteEntropyDensity.entropy_transport, heq] using h

end
end ENT.Small
