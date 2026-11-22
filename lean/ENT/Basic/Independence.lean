module

public import ENT.Basic.Uniform
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Tactic.FunProp

/-! Independence and the convolution law for the first nontrivial dimension. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT

noncomputable section

theorem cubeLaw_iIndepFun_mul {n : ℕ} (a : Fin n → ℝ) :
    iIndepFun (fun i (x : Fin n → ℝ) => a i * x i) (cubeLaw n) := by
  exact iIndepFun_pi (μ := fun _ : Fin n => uniformUnit)
    (X := fun i (x : ℝ) => a i * x)
    (fun i => (measurable_const_mul (a i)).aemeasurable)

theorem cubeLaw_map_mul_coordinate (n : ℕ) (i : Fin n) (c : ℝ) :
    (cubeLaw n).map (fun x => c * x i) = uniformUnit.map (fun x => c * x) := by
  have hmap := Measure.map_map (μ := cubeLaw n)
    (f := fun x : Fin n → ℝ => x i) (g := fun x : ℝ => c * x)
    (measurable_const_mul c) (measurable_pi_apply i)
  simpa only [Function.comp_def, cubeLaw_map_coordinate] using hmap.symm

theorem projectionLaw_two_eq_conv (a : Fin 2 → ℝ) :
    projectionLaw a = Measure.conv
      (uniformUnit.map (fun x => a 0 * x)) (uniformUnit.map (fun x => a 1 * x)) := by
  have hind := (cubeLaw_iIndepFun_mul a).indepFun (i := 0) (j := 1) (by decide)
  have hmap := hind.map_add_eq_map_conv_map (by fun_prop) (by fun_prop)
  have hp : projection a = (fun x : Fin 2 → ℝ => a 0 * x 0) +
      (fun x : Fin 2 → ℝ => a 1 * x 1) := by
    funext x
    simp [projection, Fin.sum_univ_two]
  rw [projectionLaw, hp, hmap, cubeLaw_map_mul_coordinate, cubeLaw_map_mul_coordinate]

theorem projectionLaw_two_swap (a : Fin 2 → ℝ) :
    projectionLaw (fun i => a i.rev) = projectionLaw a := by
  rw [projectionLaw_two_eq_conv, projectionLaw_two_eq_conv]
  simp only [show (0 : Fin 2).rev = 1 by decide, show (1 : Fin 2).rev = 0 by decide]
  exact Measure.conv_comm _ _

theorem projectionLaw_two_of_zero_right (a : Fin 2 → ℝ) (hzero : a 1 = 0) :
    projectionLaw a = uniformUnit.map (fun x => a 0 * x) := by
  have hp : projection a = fun x : Fin 2 → ℝ => a 0 * x 0 := by
    funext x
    simp [projection, Fin.sum_univ_two, hzero]
  rw [projectionLaw, hp, cubeLaw_map_mul_coordinate]

end
end ENT
