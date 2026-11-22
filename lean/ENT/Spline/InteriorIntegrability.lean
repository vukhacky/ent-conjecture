module

public import ENT.Spline.PositiveInterior
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Cross-entropy integrability whenever the other density has support in a
compact subinterval of the interior of the diagonal spline support. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Spline

noncomputable section

theorem continuousOn_log_diagonalSplineDensity (n : ℕ) (hn : 2 ≤ n) :
    ContinuousOn (fun x => Real.log (diagonalSplineDensity n x))
      (Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :=
  (continuous_diagonalSplineDensity n).continuousOn.log
    (fun x hx => ne_of_gt (diagonalSplineDensity_pos n hn x hx))

theorem diagonalSpline_log_bound_on_compact_interior (n : ℕ) (hn : 2 ≤ n)
    (R : ℝ) (hR : R < Real.sqrt (n : ℝ)) :
    ∃ C : ℝ, ∀ x ∈ Icc (-R) R, ‖Real.log (diagonalSplineDensity n x)‖ ≤ C := by
  apply isCompact_Icc.exists_bound_of_continuousOn
  apply (continuousOn_log_diagonalSplineDensity n hn).mono
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem integrable_mul_log_diagonalSplineDensity (n : ℕ) (hn : 2 ≤ n)
    {f : ℝ → ℝ} (hf : Integrable f volume) (R : ℝ)
    (hR : R < Real.sqrt (n : ℝ))
    (hsupport : ∀ x, x ∉ Icc (-R) R → f x = 0) :
    Integrable (fun x => f x * Real.log (diagonalSplineDensity n x)) volume := by
  have hc : ContinuousOn (fun x => Real.log (diagonalSplineDensity n x)) (Icc (-R) R) := by
    apply (continuousOn_log_diagonalSplineDensity n hn).mono
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hi := hf.integrableOn.mul_continuousOn hc isCompact_Icc
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [hsupport x hx, zero_mul]

theorem integrable_mul_diagonalSplinePotential (n : ℕ) (hn : 2 ≤ n)
    {f : ℝ → ℝ} (hf : Integrable f volume) (R : ℝ)
    (hR : R < Real.sqrt (n : ℝ))
    (hsupport : ∀ x, x ∉ Icc (-R) R → f x = 0) :
    Integrable (fun x => f x * diagonalSplinePotential n x) volume := by
  apply (integrable_mul_log_diagonalSplineDensity n hn hf R hR hsupport).neg.congr
  exact Filter.Eventually.of_forall (fun x => by
    simp only [Pi.neg_apply, diagonalSplinePotential, mul_neg])

end
end ENT.Spline
