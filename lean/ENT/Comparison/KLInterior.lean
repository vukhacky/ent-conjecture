module

public import ENT.Comparison.DensityExpectations
public import ENT.Comparison.SupportRadius
public import ENT.Entropy.Gibbs
public import ENT.Spline.InteriorIntegrability
public import ENT.Spline.DensityLaw

/-! Genuine cross-entropy integrability and support compatibility for the
non-diagonal projection. No value of a nonintegrable integral is used. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT
noncomputable section

theorem FiniteEntropyDensity.ae_nonzero_imp {μ : Measure ℝ} (p : FiniteEntropyDensity μ)
    {P : ℝ → Prop} (hμ : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂volume, p.density x ≠ 0 → P x := by
  have h : ∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (p.density x)), P x := by
    rw [← p.law_eq]
    exact hμ
  rw [ae_withDensity_iff p.measurable.ennreal_ofReal] at h
  filter_upwards [h] with x hx
  intro hp
  exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (p.nonneg x) (Ne.symm hp))))

theorem diagonalSpline_log_integrable_projection {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℝ) (ha : IsUnit a) (hdiag : ¬ IsDiagonal a) :
    Integrable (fun x => Real.log (Spline.diagonalSplineDensity n x)) (projectionLaw a) := by
  have hn0 : 0 < n := by omega
  have hr := projectionRadius_lt_sqrt_of_not_diagonal hn0 a ha hdiag
  obtain ⟨C, hC⟩ := Spline.diagonalSpline_log_bound_on_compact_interior n hn
    (projectionRadius a) hr
  exact Integrable.of_bound
    (Spline.continuous_diagonalSplineDensity n).measurable.log.aestronglyMeasurable C
    ((projectionLaw_ae_mem a).mono fun x hx => hC x hx)

def diagonalFiniteKLData {n : ℕ} (hn : 2 ≤ n) (a : Fin n → ℝ) (ha : IsUnit a)
    (hdiag : ¬ IsDiagonal a) (p : FiniteEntropyDensity (projectionLaw a)) :
    FiniteKLData p (Spline.diagonalFiniteEntropyDensity n hn) where
  cross_integrable := by
    have h := (p.integrable_iff_density
      (fun x => Real.log (Spline.diagonalSplineDensity n x))).mp
      (diagonalSpline_log_integrable_projection hn a ha hdiag)
    simpa only [Spline.diagonalFiniteEntropyDensity_density, mul_comm] using h
  support_ae := by
    have hr := projectionRadius_lt_sqrt_of_not_diagonal (by omega) a ha hdiag
    have hs := p.ae_nonzero_imp (projectionLaw_ae_mem a)
    filter_upwards [hs] with x hx
    intro hq
    by_contra hp
    have hmem := hx hp
    have hpos := Spline.diagonalSplineDensity_pos n hn x
      ⟨lt_of_lt_of_le (neg_lt_neg hr) hmem.1, lt_of_le_of_lt hmem.2 hr⟩
    exact (ne_of_gt hpos) hq

theorem FiniteKLData.potential_gap_eq_law_integrals {μ ν : Measure ℝ}
    {p : FiniteEntropyDensity μ} {q : FiniteEntropyDensity ν} (h : FiniteKLData p q) :
    (∫ x, (p.density x - q.density x) * Real.log (q.density x)) =
      (∫ x, -Real.log (q.density x) ∂ν) - (∫ x, -Real.log (q.density x) ∂μ) := by
  have hp : (∫ x, -Real.log (q.density x) ∂μ) =
      -(∫ x, p.density x * Real.log (q.density x)) := by
    rw [p.integral_eq_density]
    simp_rw [neg_mul, mul_comm (Real.log (q.density _)) (p.density _)]
    rw [integral_neg]
  have hq : (∫ x, -Real.log (q.density x) ∂ν) =
      -(∫ x, q.density x * Real.log (q.density x)) := by
    rw [q.integral_eq_density]
    simp_rw [neg_mul, mul_comm (Real.log (q.density _)) (q.density _)]
    rw [integral_neg]
  simp_rw [sub_mul]
  rw [integral_sub h.cross_integrable q.entropy_integrable, hp, hq]
  ring

end
end ENT
