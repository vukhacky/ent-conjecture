module

public import ENT.Basic.Exchangeability
public import ENT.Comparison.DensityExpectations
public import ENT.Spline.SupportInterior
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-! Integrability and cancellation of the linear Taylor term. Multiplication
by the actual density cancels the logarithmic derivative at every interior
point; the derivative vanishes at every zero of the nonnegative C1 density. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators

namespace ENT.Small
noncomputable section

theorem diagonalDensity_mul_deriv_potential (n : ℕ) (hn : 3 ≤ n) (x : ℝ) :
    Spline.diagonalSplineDensity n x * deriv (Spline.diagonalSplinePotential n) x =
      -deriv (Spline.diagonalSplineDensity n) x := by
  let q := Spline.diagonalSplineDensity n
  have hq : ContDiff ℝ 1 q := Spline.contDiff_diagonalSplineDensity 1 n (by omega)
  by_cases hx : q x = 0
  · have hmin : IsLocalMin q x := Filter.Eventually.of_forall (fun y => by
      rw [hx]
      exact Spline.diagonalSplineDensity_nonneg n (by omega) y)
    change q x * deriv (Spline.diagonalSplinePotential n) x = -deriv q x
    rw [hx, zero_mul, hmin.deriv_eq_zero, neg_zero]
  · have hd := ((hq.differentiable (by norm_num) x).hasDerivAt.log hx).neg
    have hv := hd.deriv
    change deriv (Spline.diagonalSplinePotential n) x = -(deriv q x / q x) at hv
    change q x * deriv (Spline.diagonalSplinePotential n) x = -deriv q x
    rw [hv]
    field_simp

theorem integrable_diagonalPotential_first_deriv (n : ℕ) (hn : 3 ≤ n) :
    Integrable (deriv (Spline.diagonalSplinePotential n)) (projectionLaw (diagonal n)) := by
  have hq : ContDiff ℝ 1 (Spline.diagonalSplineDensity n) :=
    Spline.contDiff_diagonalSplineDensity 1 n (by omega)
  have hi : Integrable (deriv (Spline.diagonalSplineDensity n)) volume :=
    (hq.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
    (Spline.hasCompactSupport_diagonalSplineDensity n (by omega)).deriv
  let p := Spline.diagonalFiniteEntropyDensity n (by omega)
  apply (p.integrable_iff_density _).mpr
  convert hi.neg using 1
  funext x
  change deriv (Spline.diagonalSplinePotential n) x * Spline.diagonalSplineDensity n x = _
  rw [mul_comm]
  exact diagonalDensity_mul_deriv_potential n hn x

theorem integrable_cube_diagonalPotential_first_deriv (n : ℕ) (hn : 3 ≤ n) :
    Integrable (fun x => deriv (Spline.diagonalSplinePotential n) (projection (diagonal n) x))
      (cubeLaw n) := by
  have h := integrable_map_measure
    (μ := cubeLaw n) (measurable_deriv (Spline.diagonalSplinePotential n)).aestronglyMeasurable
    (measurable_projection (diagonal n)).aemeasurable
  exact h.mp (integrable_diagonalPotential_first_deriv n hn)

theorem integrable_linear_potential_term {n : ℕ} (hn : 3 ≤ n) (b : Fin n → ℝ) :
    Integrable (fun x => deriv (Spline.diagonalSplinePotential n) (projection (diagonal n) x) *
      projection b x) (cubeLaw n) := by
  have h := (integrable_cube_diagonalPotential_first_deriv n hn).bdd_mul
    (measurable_projection b).aestronglyMeasurable
    ((cubeLaw_ae_mem n).mono fun x hx => by
      simpa only [Real.norm_eq_abs] using abs_projection_le_radius b x hx)
  simpa only [mul_comm] using h

theorem integral_linear_potential_term {n : ℕ} (hn : 3 ≤ n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) :
    (∫ x, deriv (Spline.diagonalSplinePotential n) (projection (diagonal n) x) *
      projection b x ∂cubeLaw n) = 0 := by
  simpa only [mul_comm] using integral_zero_sum_projection_diagonal_test (by omega) b hb
    (integrable_cube_diagonalPotential_first_deriv n hn)

end
end ENT.Small
