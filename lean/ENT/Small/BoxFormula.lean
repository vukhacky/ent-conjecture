module

public import ENT.Small.BoxPrimitive
public import Mathlib.Tactic.FieldSimp

/-! Inclusion-exclusion for three genuine independent uniform averages. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Small

noncomputable section

def centralDifference (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x + a) - f (x - a)

theorem continuous_centralDifference (a : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (centralDifference a f) := by
  unfold centralDifference
  exact (hf.comp (continuous_id.add continuous_const)).sub
    (hf.comp (continuous_id.sub continuous_const))

theorem integrable_continuous_uniformUnit {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f uniformUnit := by
  unfold uniformUnit
  exact (hf.continuousOn.integrableOn_compact isCompact_Icc).smul_measure (by norm_num)

theorem boxAverage_const_mul (a k : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    boxAverage a (fun y => k * f y) x = k * boxAverage a f x := by
  unfold boxAverage
  exact integral_const_mul k _

theorem boxAverage_shift (a d : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    boxAverage a (fun y => f (y + d)) x = boxAverage a f (x + d) := by
  unfold boxAverage
  congr 1
  funext y
  congr 1
  ring

theorem boxAverage_comm_centralDifference (a b : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) (x : ℝ) :
    boxAverage a (centralDifference b f) x = centralDifference b (boxAverage a f) x := by
  have hp : Integrable (fun u : ℝ => f (x + a * u + b)) uniformUnit :=
    integrable_continuous_uniformUnit (hf.comp (by fun_prop))
  have hm : Integrable (fun u : ℝ => f (x + a * u - b)) uniformUnit :=
    integrable_continuous_uniformUnit (hf.comp (by fun_prop))
  unfold centralDifference boxAverage
  rw [integral_sub hp hm]
  congr 1 <;> (congr 1; funext u; congr 1; ring)

theorem centralDifference_const_mul (a k : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    centralDifference a (fun y => k * f y) x = k * centralDifference a f x := by
  unfold centralDifference
  ring

theorem boxAverage_three_primitive {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b)
    {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (x : ℝ) :
    boxAverage a (boxAverage b (boxAverage c f)) x =
      ((2 * a) * (2 * b) * (2 * c))⁻¹ *
        centralDifference c (centralDifference b (centralDifference a (boxPrimitive f 3))) x := by
  have hfirst : boxAverage c f = fun y => (2 * c)⁻¹ * centralDifference c (boxPrimitive f 1) y := by
    funext y
    exact boxAverage_primitive hf hc 0 y
  have hsecond : boxAverage b (boxPrimitive f 1) =
      fun y => (2 * b)⁻¹ * centralDifference b (boxPrimitive f 2) y := by
    funext y
    exact boxAverage_primitive hf hb 1 y
  have hthird : boxAverage a (boxPrimitive f 2) =
      fun y => (2 * a)⁻¹ * centralDifference a (boxPrimitive f 3) y := by
    funext y
    exact boxAverage_primitive hf ha 2 y
  have hlin (u k : ℝ) (g : ℝ → ℝ) :
      boxAverage u (fun y => k * g y) = fun y => k * boxAverage u g y := by
    funext y
    exact boxAverage_const_mul u k g y
  have hcomm (u v : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
      boxAverage u (centralDifference v g) = centralDifference v (boxAverage u g) := by
    funext y
    exact boxAverage_comm_centralDifference u v hg y
  have hdlin (u k : ℝ) (g : ℝ → ℝ) :
      centralDifference u (fun y => k * g y) = fun y => k * centralDifference u g y := by
    funext y
    exact centralDifference_const_mul u k g y
  have htwo : boxAverage b (boxAverage c f) = fun y => (2 * c)⁻¹ *
      ((2 * b)⁻¹ * centralDifference c (centralDifference b (boxPrimitive f 2)) y) := by
    rw [hfirst, hlin, hcomm b c _ (continuous_boxPrimitive_succ hf 0), hsecond, hdlin]
  rw [htwo, hlin, hlin,
    hcomm a c _ (continuous_centralDifference b (continuous_boxPrimitive_succ hf 1)),
    hcomm a b _ (continuous_boxPrimitive_succ hf 1), hthird, hdlin, hdlin]
  simp only [mul_inv]
  ring

theorem centralDifference_three_odd {F : ℝ → ℝ} (hF : Function.Odd F) (a b c : ℝ) :
    centralDifference c (centralDifference b (centralDifference a F)) 0 =
      2 * (F (a + b + c) - F (-a + b + c) - F (a - b + c) - F (a + b - c)) := by
  unfold centralDifference
  simp only [zero_add, zero_sub]
  have h1 : F (c - b - a) = -F (a + b - c) := by
    convert hF (a + b - c) using 1 <;> congr 1 <;> ring
  have h2 : F (-c + b - a) = -F (a - b + c) := by
    convert hF (a - b + c) using 1 <;> congr 1 <;> ring
  have h3 : F (-c - b + a) = -F (-a + b + c) := by
    convert hF (-a + b + c) using 1 <;> congr 1 <;> ring
  have h4 : F (-c - b - a) = -F (a + b + c) := by
    convert hF (a + b + c) using 1 <;> congr 1 <;> ring
  rw [h1, h2, h3, h4]
  have heq1 : c + b + a = a + b + c := by ring
  have heq2 : c + b - a = -a + b + c := by ring
  have heq3 : c - b + a = a - b + c := by ring
  have heq4 : -c + b + a = a + b - c := by ring
  rw [heq1, heq2, heq3, heq4]
  ring

/-- The source's four-term formula, for the actual pushforward of three iid uniforms. -/
theorem integral_projection_three_primitive (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f) :
    (∫ x, f x ∂projectionLaw a) =
      (boxPrimitive f 3 (a 0 + a 1 + a 2) - boxPrimitive f 3 (-a 0 + a 1 + a 2) -
        boxPrimitive f 3 (a 0 - a 1 + a 2) - boxPrimitive f 3 (a 0 + a 1 - a 2)) /
          (4 * a 0 * a 1 * a 2) := by
  have hodd : Function.Odd (boxPrimitive f 3) := by
    intro x
    have h := boxPrimitive_parity heven 3 x
    norm_num only [pow_succ, pow_zero, mul_one, neg_mul, one_mul, neg_neg] at h
    exact h
  rw [integral_projection_three_eq_boxAverage a ha hf,
    boxAverage_three_primitive (fun _ _ => hf.intervalIntegrable) (ha 0).ne' (ha 1).ne' (ha 2).ne',
    centralDifference_three_odd hodd]
  field_simp
  ring

end
end ENT.Small
