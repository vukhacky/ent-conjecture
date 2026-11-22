module

public import ENT.Basic.Coefficients
public import ENT.Basic.Uniform
public import ENT.Entropy.LawInvariance
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! The complete one-dimensional ENT statement. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ENT

noncomputable section

theorem projectionLaw_eq_uniformUnit_one {a : Fin 1 → ℝ} (ha : IsUnit a) :
    projectionLaw a = uniformUnit := by
  rcases isUnit_one_iff.mp ha with hpos | hneg
  · have hp : projection a = fun x : Fin 1 → ℝ => x 0 := by
      funext x
      simp [projection, hpos]
    rw [projectionLaw, hp]
    exact cubeLaw_map_coordinate 1 0
  · have hp : projection a = (fun x : ℝ => -x) ∘ (fun x : Fin 1 → ℝ => x 0) := by
      funext x
      simp [projection, hneg]
    rw [projectionLaw, hp,
      ← Measure.map_map (f := fun x : Fin 1 → ℝ => x 0) (g := fun x : ℝ => -x)
        measurable_neg (measurable_pi_apply 0),
      cubeLaw_map_coordinate, uniformUnit_map_neg]

@[simp]
theorem isUnit_diagonal_one : IsUnit (diagonal 1) := by
  simp [IsUnit, diagonal]

theorem ent_one : ENTAt 1 := by
  intro a ha
  let p := uniformFiniteEntropyDensity.transport (projectionLaw_eq_uniformUnit_one ha).symm
  let q := uniformFiniteEntropyDensity.transport
    (projectionLaw_eq_uniformUnit_one isUnit_diagonal_one).symm
  have hp : p.entropy = Real.log 2 := by
    simp [p]
  have hq : q.entropy = Real.log 2 := by
    simp [q]
  have heq : p.entropy = q.entropy := hp.trans hq.symm
  exact ⟨p, q, heq.le, ⟨fun _ => isDiagonal_of_isUnit_one ha, fun _ => heq⟩⟩

end
end ENT
