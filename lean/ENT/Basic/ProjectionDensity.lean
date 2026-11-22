module

public import ENT.Basic.ScaledUniform
public import ENT.Basic.Symmetry
public import ENT.Basic.ProjectionSupport
public import ENT.Basic.ProjectionConvolution
public import ENT.Entropy.Convolution
public import Mathlib.Tactic.NormNum

/-!
Every nondegenerate finite uniform projection has an actual bounded, compactly
supported probability density with integrable `f log f`.  Zero coefficients are
allowed: only the selected anchor must be nonzero.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace ENT

noncomputable section

def projectionFiniteEntropyDensityOfPositiveAnchor {n : ℕ}
    (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hi : 0 < a i) :
    FiniteEntropyDensity (projectionLaw a) :=
  (convolutionFiniteEntropyDensity (scaledUniformFiniteEntropyDensity (a i) hi)
    (projectionLaw (removeCoefficient a i)) ((2 * a i)⁻¹) (a i)
    (projectionRadius (removeCoefficient a i))
    (scaledUniformDensity_le hi)
    (scaledUniformDensity_eq_zero_of_not_mem (a i))
    (projectionLaw_ae_mem (removeCoefficient a i))).transport
      (projectionLaw_eq_conv_remove a i).symm

theorem exists_abs_pos_of_isUnit {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ i, 0 < |a i| := by
  have hsum : 0 < ∑ i, (a i) ^ 2 := by rw [ha]; norm_num
  obtain ⟨i, _, hi⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ => sq_nonneg (a i))).mp hsum
  refine ⟨i, abs_pos.mpr ?_⟩
  intro hi0
  simp only [hi0, zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hi

def projectionFiniteEntropyDensity {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    FiniteEntropyDensity (projectionLaw a) := by
  cases n with
  | zero =>
      have h := ha
      simp only [IsUnit, Finset.univ_eq_empty, Finset.sum_empty] at h
      exact False.elim (zero_ne_one h)
  | succ n =>
      let i := Classical.choose (exists_abs_pos_of_isUnit a ha)
      have hi : 0 < |a i| := Classical.choose_spec (exists_abs_pos_of_isUnit a ha)
      exact (projectionFiniteEntropyDensityOfPositiveAnchor (fun j => |a j|) i hi).transport
        (projectionLaw_abs a)

theorem densityExistence : DensityExistence := by
  intro n _ a ha
  exact ⟨projectionFiniteEntropyDensity a ha⟩

end
end ENT
