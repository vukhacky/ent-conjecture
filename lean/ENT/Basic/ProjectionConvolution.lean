module

public import ENT.Basic.Uniform
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FunProp

/-! Splitting an arbitrary coefficient from a finite independent uniform sum. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace ENT

noncomputable section

def removeCoefficient {n : ℕ} (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Fin n → ℝ :=
  fun j => a (i.succAbove j)

theorem projectionLaw_eq_conv_remove {n : ℕ} (a : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    projectionLaw a = Measure.conv (uniformUnit.map (fun x => a i * x))
      (projectionLaw (removeCoefficient a i)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let f : ℝ × (Fin n → ℝ) → ℝ := fun z => a i * z.1 + projection (removeCoefficient a i) z.2
  have hf : Measurable f := by dsimp [f, projection]; fun_prop
  have he : (cubeLaw (n + 1)).map e = uniformUnit.prod (cubeLaw n) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => uniformUnit) i).map_eq
  have hsum : projection a = f ∘ e := by
    funext x
    simp only [projection, Function.comp_apply, f, e, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv, removeCoefficient]
    exact Fin.sum_univ_succAbove (fun j => a j * x j) i
  calc
    _ = (uniformUnit.prod (cubeLaw n)).map f := by
      rw [projectionLaw, hsum, ← Measure.map_map hf e.measurable, he]
    _ = _ := by
      unfold Measure.conv projectionLaw
      rw [Measure.map_prod_map uniformUnit (cubeLaw n)
        (measurable_const_mul (a i)) (measurable_projection (removeCoefficient a i)),
        Measure.map_map (f := Prod.map (fun x => a i * x) (projection (removeCoefficient a i)))
          (g := fun z : ℝ × ℝ => z.1 + z.2) (by fun_prop)
          ((measurable_const_mul (a i)).prodMap
            (measurable_projection (removeCoefficient a i)))]
      rfl

end
end ENT
