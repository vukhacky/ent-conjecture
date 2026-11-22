module

public import ENT.Basic.ProjectionDensity

/-! Explicit bounds for the genuine density constructed from a positive anchor. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace ENT

noncomputable section

@[simp]
theorem FiniteEntropyDensity.density_transport {μ ν : Measure ℝ}
    (p : FiniteEntropyDensity μ) (h : μ = ν) : (p.transport h).density = p.density := by
  subst ν
  rfl

theorem projectionFiniteEntropyDensityOfPositiveAnchor_density {n : ℕ}
    (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hi : 0 < a i) :
    (projectionFiniteEntropyDensityOfPositiveAnchor a i hi).density =
      convolutionDensity (projectionLaw (removeCoefficient a i)) (scaledUniformDensity (a i)) := by
  simp only [projectionFiniteEntropyDensityOfPositiveAnchor, FiniteEntropyDensity.density_transport]
  rfl

theorem projectionFiniteEntropyDensityOfPositiveAnchor_le {n : ℕ}
    (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hi : 0 < a i) (x : ℝ) :
    (projectionFiniteEntropyDensityOfPositiveAnchor a i hi).density x ≤ (2 * a i)⁻¹ := by
  rw [projectionFiniteEntropyDensityOfPositiveAnchor_density]
  exact convolutionDensity_le _ (by positivity) (scaledUniformDensity_le hi) x

theorem projectionRadius_eq_remove {n : ℕ} (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    projectionRadius a = |a i| + projectionRadius (removeCoefficient a i) :=
  Fin.sum_univ_succAbove (fun j => |a j|) i

theorem projectionFiniteEntropyDensityOfPositiveAnchor_support {n : ℕ}
    (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hi : 0 < a i) (x : ℝ)
    (hx : x ∉ Set.Icc (-projectionRadius a) (projectionRadius a)) :
    (projectionFiniteEntropyDensityOfPositiveAnchor a i hi).density x = 0 := by
  rw [projectionFiniteEntropyDensityOfPositiveAnchor_density]
  rw [projectionRadius_eq_remove a i, abs_of_pos hi] at hx
  exact convolutionDensity_eq_zero_of_not_mem _
    (scaledUniformDensity_eq_zero_of_not_mem (a i))
    (projectionLaw_ae_mem (removeCoefficient a i)) x hx

theorem projectionLaw_smul {n : ℕ} (a : Fin n → ℝ) (c : ℝ) :
    projectionLaw (fun i => c * a i) = (projectionLaw a).map (fun x => c * x) := by
  rw [projectionLaw, projectionLaw, Measure.map_map (measurable_const_mul c) (measurable_projection a)]
  congr 1
  funext x
  simp only [projection, Function.comp_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem projection_density_ae_bound_of_positive_anchor {n : ℕ} (a : Fin n → ℝ)
    (i : Fin n) (hi : 0 < a i) (p : FiniteEntropyDensity (projectionLaw a)) :
    ∀ᵐ x ∂volume, p.density x ≤ (2 * a i)⁻¹ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      let q := projectionFiniteEntropyDensityOfPositiveAnchor a i hi
      filter_upwards [p.density_ae_eq q] with x hx
      rw [hx]
      exact projectionFiniteEntropyDensityOfPositiveAnchor_le a i hi x

theorem projection_density_exists_ae_bound {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a)
    (p : FiniteEntropyDensity (projectionLaw a)) :
    ∃ M : ℝ, ∀ᵐ x ∂volume, p.density x ≤ M := by
  obtain ⟨i, hi⟩ := exists_abs_pos_of_isUnit a ha
  have h := projection_density_ae_bound_of_positive_anchor (fun j => |a j|) i hi
    (p.transport (projectionLaw_abs a).symm)
  simpa only [FiniteEntropyDensity.density_transport] using
    (show ∃ M : ℝ, ∀ᵐ x ∂volume, (p.transport (projectionLaw_abs a).symm).density x ≤ M
      from ⟨(2 * |a i|)⁻¹, h⟩)

end
end ENT
