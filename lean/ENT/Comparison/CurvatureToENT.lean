module

public import ENT.Comparison.EntropyFromPotential
public import ENT.Spline.CurvatureData
public import Mathlib.Topology.Order.LeftRightNhds

/-! Generic curvature-to-ENT assembly for the actual diagonal spline law.
Curvature on the positive open half is extended to zero by continuity.
The hypothesis remains explicit until a finite checker or Pang discharges it. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology

namespace ENT
noncomputable section

namespace Comparison

theorem nonneg_at_zero_of_positive_half {f : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousAt f 0) (hpos : ∀ x ∈ Ioo (0 : ℝ) R, 0 ≤ f x) : 0 ≤ f 0 := by
  have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)] with x hx0 hxR
  exact hpos x ⟨hx0, hxR⟩

end Comparison

theorem diagonalSpline_curvaturePotential_of_positive_half {n : ℕ} (hn : 5 ≤ n)
    (hcurv : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt n),
      0 ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x) :
    Comparison.CurvaturePotential (Real.sqrt n) (Spline.diagonalSplinePotential n) := by
  have hR : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hsmooth (x : ℝ) (hx : x ∈ Ioo (-Real.sqrt n) (Real.sqrt n)) :
      ContDiffAt ℝ 3 (Spline.diagonalSplinePotential n) x :=
    Spline.contDiffAt_diagonalSplinePotential 3 n (by omega) x
      (ne_of_gt (Spline.diagonalSplineDensity_pos n (by omega) x hx))
  refine ⟨hR, ?_, ?_, hsmooth, ?_⟩
  · exact (Spline.continuous_diagonalSplineDensity n).measurable.log.neg
  · intro x
    unfold Spline.diagonalSplinePotential
    rw [Spline.diagonalSplineDensity_even n (by omega)]
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with hzero | hpositive
    · subst x
      have h0 := hsmooth 0 ⟨by linarith, hR⟩
      have h1 : ContDiffAt ℝ 2 (deriv (Spline.diagonalSplinePotential n)) 0 :=
        h0.derivWithin (by norm_num)
      have h2 : ContDiffAt ℝ 1 (deriv (deriv (Spline.diagonalSplinePotential n))) 0 :=
        h1.derivWithin (by norm_num)
      have h3 : ContDiffAt ℝ 0 (deriv (deriv (deriv (Spline.diagonalSplinePotential n)))) 0 :=
        h2.derivWithin (by norm_num)
      exact Comparison.nonneg_at_zero_of_positive_half hR h3.continuousAt hcurv
    · exact hcurv x ⟨hpositive, hx.2⟩

theorem entAt_of_spline_curvature {n : ℕ} (hn : 5 ≤ n)
    (hcurv : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt n),
      0 ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x) : ENTAt n := by
  apply entAt_of_diagonal_potential_comparison (by omega)
  exact (diagonalSpline_curvaturePotential_of_positive_half hn hcurv).expectation_le
    (by omega) (Spline.ae_mem_diagonalSplineSupport n (by omega))
    (Spline.diagonalSplinePotential_integrable n (by omega))

theorem entAt_of_cellwise_curvature {n : ℕ} (hn : 5 ≤ n)
    (hcert : Spline.CellwiseCurvature n) : ENTAt n :=
  entAt_of_diagonal_potential_comparison (by omega)
    (Spline.diagonalSplinePotential_expectation_le n hn hcert)

end
end ENT
