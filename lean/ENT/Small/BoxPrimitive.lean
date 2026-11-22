module

public import ENT.Basic.ProjectionDensityBounds
public import ENT.Basic.Independence
public import ENT.Entropy.Gibbs
public import ENT.Comparison.DensityExpectations
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.FunProp

/-! Actual uniform averages and iterated primitives. The zeroth integrand may have
integrable logarithmic singularities; no endpoint continuity is assumed for it. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Small

noncomputable section

def boxPrimitive (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | n + 1 => fun x => ∫ y in 0..x, boxPrimitive f n y

@[simp] theorem boxPrimitive_zero (f : ℝ → ℝ) : boxPrimitive f 0 = f := rfl

@[simp] theorem boxPrimitive_succ (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    boxPrimitive f (n + 1) x = ∫ y in 0..x, boxPrimitive f n y := rfl

@[simp] theorem boxPrimitive_succ_zero (f : ℝ → ℝ) (n : ℕ) :
    boxPrimitive f (n + 1) 0 = 0 := by simp

theorem continuous_boxPrimitive_succ {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (n : ℕ) :
    Continuous (boxPrimitive f (n + 1)) := by
  induction n with
  | zero => exact intervalIntegral.continuous_primitive hf 0
  | succ n ih => exact intervalIntegral.continuous_primitive (fun a b => ih.intervalIntegrable a b) 0

theorem intervalIntegrable_boxPrimitive {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (boxPrimitive f n) volume a b := by
  cases n with
  | zero => exact hf a b
  | succ n => exact (continuous_boxPrimitive_succ hf n).intervalIntegrable a b

theorem hasDerivAt_boxPrimitive_succ_succ {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (n : ℕ) (x : ℝ) :
    HasDerivAt (boxPrimitive f (n + 2)) (boxPrimitive f (n + 1) x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_boxPrimitive hf (n + 1) 0 x)
    (continuous_boxPrimitive_succ hf n).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_boxPrimitive_succ hf n).continuousAt

theorem boxPrimitive_sub_eq_integral {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (n : ℕ) (a b : ℝ) :
    boxPrimitive f (n + 1) b - boxPrimitive f (n + 1) a =
      ∫ x in a..b, boxPrimitive f n x := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_boxPrimitive hf n 0 a) (intervalIntegrable_boxPrimitive hf n a b)
  change (∫ x in 0..b, boxPrimitive f n x) - (∫ x in 0..a, boxPrimitive f n x) = _
  linarith

theorem boxPrimitive_parity {f : ℝ → ℝ} (hf : Function.Even f) (n : ℕ) (x : ℝ) :
    boxPrimitive f n (-x) = (-1 : ℝ) ^ n * boxPrimitive f n x := by
  induction n generalizing x with
  | zero => simpa only [boxPrimitive_zero, pow_zero, one_mul] using hf x
  | succ n ih =>
      have hneg : (∫ y in 0..-x, boxPrimitive f n y) =
          -(∫ y in 0..x, boxPrimitive f n (-y)) := by
        rw [intervalIntegral.integral_comp_neg, neg_zero, intervalIntegral.integral_symm]
      simp only [boxPrimitive_succ]
      rw [hneg]
      have heq : (fun y : ℝ => boxPrimitive f n (-y)) =
          (fun y => (-1 : ℝ) ^ n * boxPrimitive f n y) := by
        funext y
        exact ih y
      rw [heq, intervalIntegral.integral_const_mul, pow_succ]
      ring

def boxAverage (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u, f (x + a * u) ∂uniformUnit

theorem boxAverage_eq_interval {a : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ) (x : ℝ) :
    boxAverage a f x = (2 * a)⁻¹ * ∫ y in x - a..x + a, f y := by
  unfold boxAverage
  rw [uniformUnit, integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_add_mul (f := f) ha x]
  simp only [mul_neg_one, mul_one, ← sub_eq_add_neg, smul_eq_mul]
  ring

theorem boxAverage_primitive {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {a : ℝ} (ha : a ≠ 0)
    (n : ℕ) (x : ℝ) :
    boxAverage a (boxPrimitive f n) x = (2 * a)⁻¹ *
      (boxPrimitive f (n + 1) (x + a) - boxPrimitive f (n + 1) (x - a)) := by
  rw [boxAverage_eq_interval ha, ← boxPrimitive_sub_eq_integral hf]

theorem boxAverage_of_hasDerivAt {f F : ℝ → ℝ} (hf : Continuous f)
    (hF : ∀ x, HasDerivAt F (f x) x) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    boxAverage a f x = (2 * a)⁻¹ * (F (x + a) - F (x - a)) := by
  rw [boxAverage_eq_interval ha.ne']
  congr 1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith)
    (fun y _ => (hF y).continuousAt.continuousWithinAt)
    (fun y _ => hF y) (hf.intervalIntegrable _ _)

theorem integrable_projection_of_integrable {n : ℕ} (a : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (hi : 0 < a i) {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable f (projectionLaw a) := by
  let p := projectionFiniteEntropyDensityOfPositiveAnchor a i hi
  apply (p.integrable_iff_density f).mpr
  simpa only [mul_comm] using hf.bdd_mul p.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (p.nonneg x)]
      exact projectionFiniteEntropyDensityOfPositiveAnchor_le a i hi x)

theorem projectionLaw_three_eq_conv (a : Fin 3 → ℝ) :
    projectionLaw a = Measure.conv (uniformUnit.map (fun x => a 0 * x))
      (Measure.conv (uniformUnit.map (fun x => a 1 * x))
        (uniformUnit.map (fun x => a 2 * x))) := by
  rw [projectionLaw_eq_conv_remove a 0, projectionLaw_two_eq_conv]
  rfl

theorem integral_projection_three_eq_boxAverage (a : Fin 3 → ℝ)
    (ha : ∀ i, 0 < a i) {f : ℝ → ℝ} (hf : Integrable f) :
    (∫ x, f x ∂projectionLaw a) = boxAverage (a 0) (boxAverage (a 1) (boxAverage (a 2) f)) 0 := by
  have hi := integrable_projection_of_integrable a 0 (ha 0) hf
  rw [projectionLaw_three_eq_conv] at hi ⊢
  rw [integral_conv hi, (measurableEmbedding_mulLeft₀ (ha 0).ne').integral_map]
  unfold boxAverage
  simp only [zero_add]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  have hi2 : Integrable (fun y => f (a 0 * u + y))
      (Measure.conv (uniformUnit.map (fun x => a 1 * x))
        (uniformUnit.map (fun x => a 2 * x))) := by
    have h := integrable_projection_of_integrable (fun i : Fin 2 => a i.succ) 0 (ha 1)
      (hf.comp_add_left (a 0 * u))
    rwa [projectionLaw_two_eq_conv] at h
  dsimp only
  rw [integral_conv hi2, (measurableEmbedding_mulLeft₀ (ha 1).ne').integral_map]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  rw [(measurableEmbedding_mulLeft₀ (ha 2).ne').integral_map]
  congr 1
  funext w
  rw [add_assoc]

end
end ENT.Small
