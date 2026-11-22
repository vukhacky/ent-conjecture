module

public import ENT.Basic.Uniform
public import ENT.Basic.Coefficients
public import Mathlib.Tactic.FunProp

/-! Changing the signs of coefficients preserves the projection law. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace ENT

noncomputable section

def signReflection {n : ℕ} (a : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if a i < 0 then -x i else x i

theorem measurable_signReflection {n : ℕ} (a : Fin n → ℝ) :
    Measurable (signReflection a) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases h : a i < 0
  · simp only [signReflection, h, ite_true]
    fun_prop
  · simpa only [signReflection, h, ite_false] using (measurable_pi_apply i)

theorem cubeLaw_map_signReflection {n : ℕ} (a : Fin n → ℝ) :
    (cubeLaw n).map (signReflection a) = cubeLaw n := by
  have hm : ∀ i : Fin n,
      Measurable (fun x : ℝ => if a i < 0 then -x else x) := by
    intro i
    by_cases h : a i < 0 <;> simp only [h, ite_true, ite_false] <;> fun_prop
  change (Measure.pi (fun _ : Fin n => uniformUnit)).map
    (fun x i => if a i < 0 then -x i else x i) = Measure.pi (fun _ : Fin n => uniformUnit)
  rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  congr 1
  funext i
  by_cases h : a i < 0
  · simpa only [h, ite_true] using uniformUnit_map_neg
  · simp only [h, ite_false, Measure.map_id']

theorem projection_abs_eq_comp_signReflection {n : ℕ} (a : Fin n → ℝ) :
    projection (fun i => |a i|) = projection a ∘ signReflection a := by
  funext x
  unfold projection
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : a i < 0
  · simp [signReflection, h, abs_of_neg h]
  · simp [signReflection, h, abs_of_nonneg (le_of_not_gt h)]

theorem projectionLaw_abs {n : ℕ} (a : Fin n → ℝ) :
    projectionLaw (fun i => |a i|) = projectionLaw a := by
  unfold projectionLaw
  rw [projection_abs_eq_comp_signReflection,
    ← Measure.map_map (measurable_projection a) (measurable_signReflection a),
    cubeLaw_map_signReflection]

theorem projectionLaw_eq_diagonal_of_isDiagonal {n : ℕ} (a : Fin n → ℝ)
    (ha : IsDiagonal a) : projectionLaw a = projectionLaw (diagonal n) := by
  have habs : (fun i => |a i|) = diagonal n := funext ((isDiagonal_iff_abs a).mp ha)
  rw [← projectionLaw_abs a, habs]

end
end ENT
