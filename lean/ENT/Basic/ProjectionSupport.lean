module

public import ENT.Basic.Uniform
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! Almost-sure compact support of every finite uniform projection. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace ENT

noncomputable section

theorem uniformUnit_ae_mem : ∀ᵐ x ∂uniformUnit, x ∈ Set.Icc (-1) 1 := by
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem cubeLaw_ae_mem (n : ℕ) :
    ∀ᵐ x ∂cubeLaw n, ∀ i, x i ∈ Set.Icc (-1) 1 := by
  apply ae_all_iff.mpr
  intro i
  have h := uniformUnit_ae_mem
  rw [← cubeLaw_map_coordinate n i] at h
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h

def projectionRadius {n : ℕ} (a : Fin n → ℝ) : ℝ := ∑ i, |a i|

theorem projectionRadius_nonneg {n : ℕ} (a : Fin n → ℝ) :
    0 ≤ projectionRadius a := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_projection_le_radius {n : ℕ} (a x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (-1) 1) : |projection a x| ≤ projectionRadius a := by
  unfold projection projectionRadius
  calc
    _ ≤ ∑ i, |a i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hxi : |x i| ≤ 1 := abs_le.mpr (hx i)
      nlinarith [abs_nonneg (a i)]

theorem projectionLaw_ae_mem {n : ℕ} (a : Fin n → ℝ) :
    ∀ᵐ y ∂projectionLaw a, y ∈ Set.Icc (-projectionRadius a) (projectionRadius a) := by
  apply (ae_map_iff (measurable_projection a).aemeasurable measurableSet_Icc).mpr
  filter_upwards [cubeLaw_ae_mem n] with x hx
  exact abs_le.mp (abs_projection_le_radius a x hx)

end
end ENT
