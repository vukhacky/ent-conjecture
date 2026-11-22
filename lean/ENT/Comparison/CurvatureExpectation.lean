module

public import ENT.Comparison.GenericContraction
public import ENT.Comparison.GlobalBalancing
public import ENT.Basic.ProjectionMoments
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Global expectation comparison from nonnegative third derivative of an
even potential. A quadratic correction enables monotone radial contraction;
equal second moments remove that correction after dominated convergence. -/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace ENT.Comparison.CurvaturePotential

noncomputable section

def radialSequence (m : ℕ) : ℝ := 1 - 1 / ((m : ℝ) + 1)

theorem radialSequence_mem (m : ℕ) : radialSequence m ∈ Ico 0 1 := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hd : 0 < (m : ℝ) + 1 := by positivity
  have hi : 1 / ((m : ℝ) + 1) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hp : 0 < 1 / ((m : ℝ) + 1) := one_div_pos.mpr hd
  exact ⟨by unfold radialSequence; linarith, by unfold radialSequence; linarith⟩

theorem radialSequence_tendsto : Tendsto radialSequence atTop (𝓝 1) := by
  change Tendsto (fun m : ℕ => 1 - 1 / ((m : ℝ) + 1)) atTop (𝓝 1)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [sub_zero] using h

variable {n : ℕ} {V : ℝ → ℝ} (J : CurvaturePotential (Real.sqrt n) V)

include J

theorem contracted_expectation_le (hn : 0 < n) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, corrected V (ρ * x) ∂projectionLaw a) ≤
      ∫ x, corrected V (ρ * x) ∂projectionLaw (diagonal n) := by
  let K := J.contractionJet ρ hρ0 hρ1
  obtain ⟨C, hC⟩ := J.contraction_bounded ρ hρ0 hρ1
  have h := K.expectation_le_diagonal hn hC (J.clipRadius_gt ρ hρ0 hρ1) a ha
  rw [potentialExpectation_eq_integral_law _ K.continuous,
    potentialExpectation_eq_integral_law _ K.continuous] at h
  have heq (b : Fin n → ℝ) (hb : IsUnit b) :
      (∫ x, clipped V ρ (clipRadius (Real.sqrt n) ρ) x ∂projectionLaw b) =
        ∫ x, corrected V (ρ * x) ∂projectionLaw b := by
    apply integral_congr_ae
    apply (projectionLaw_ae_mem b).mono
    intro x hx
    have hR := projectionRadius_le_sqrt b hb
    exact J.contraction_eq ρ hρ0 hρ1
      ⟨(neg_le_neg hR).trans hx.1, hx.2.trans hR⟩
  rwa [heq a ha, heq (diagonal n) (isUnit_diagonal hn)] at h

theorem projection_integrable (hn : 0 < n)
    (hV : Integrable V (projectionLaw (diagonal n))) (a : Fin n → ℝ) (ha : IsUnit a) :
    Integrable V (projectionLaw a) := by
  by_cases hdiag : IsDiagonal a
  · rw [projectionLaw_eq_diagonal_of_isDiagonal a hdiag]
    exact hV
  · exact J.integrable_of_ae_bounded_support (projectionRadius a)
      (projectionRadius_lt_sqrt_of_not_diagonal hn a ha hdiag) (projectionLaw_ae_mem a)

theorem projection_ae_interior (hn : 0 < n)
    (hdiag : ∀ᵐ x ∂projectionLaw (diagonal n), x ∈ Ioo (-Real.sqrt n) (Real.sqrt n))
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∀ᵐ x ∂projectionLaw a, x ∈ Ioo (-Real.sqrt n) (Real.sqrt n) := by
  by_cases hflat : IsDiagonal a
  · rw [projectionLaw_eq_diagonal_of_isDiagonal a hflat]
    exact hdiag
  · have hr := projectionRadius_lt_sqrt_of_not_diagonal hn a ha hflat
    exact (projectionLaw_ae_mem a).mono fun x hx =>
      ⟨lt_of_lt_of_le (neg_lt_neg hr) hx.1, lt_of_le_of_lt hx.2 hr⟩

theorem corrected_expectation_le (hn : 0 < n)
    (hdiag : ∀ᵐ x ∂projectionLaw (diagonal n), x ∈ Ioo (-Real.sqrt n) (Real.sqrt n))
    (hV : Integrable V (projectionLaw (diagonal n))) (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, corrected V x ∂projectionLaw a) ≤ ∫ x, corrected V x ∂projectionLaw (diagonal n) := by
  have hbound : ∀ᶠ m in atTop, radialSequence m ∈ Icc 0 1 :=
    Filter.Eventually.of_forall fun m =>
      ⟨(radialSequence_mem m).1, (radialSequence_mem m).2.le⟩
  have hp := J.corrected_integral_tendsto (J.projection_ae_interior hn hdiag a ha)
    (J.projection_integrable hn hV a ha) radialSequence hbound radialSequence_tendsto
  have hq := J.corrected_integral_tendsto hdiag hV radialSequence hbound radialSequence_tendsto
  exact le_of_tendsto_of_tendsto' hp hq fun m =>
    J.contracted_expectation_le hn _ (radialSequence_mem m).1 (radialSequence_mem m).2 a ha

/-- The quadratic correction disappears because normalized uniform
projections all have second moment `1 / 3`. -/
theorem expectation_le (hn : 0 < n)
    (hdiag : ∀ᵐ x ∂projectionLaw (diagonal n), x ∈ Ioo (-Real.sqrt n) (Real.sqrt n))
    (hV : Integrable V (projectionLaw (diagonal n))) (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, V x ∂projectionLaw a) ≤ ∫ x, V x ∂projectionLaw (diagonal n) := by
  apply (J.integral_corrected_le_iff (J.projection_ae_interior hn hdiag a ha) hdiag
    (J.projection_integrable hn hV a ha) hV ?_).mp
  · exact J.corrected_expectation_le hn hdiag hV a ha
  · rw [integral_projectionLaw_sq_of_isUnit a ha,
      integral_projectionLaw_sq_of_isUnit (diagonal n) (isUnit_diagonal hn)]

end
end ENT.Comparison.CurvaturePotential
