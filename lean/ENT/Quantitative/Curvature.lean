module

public import ENT.Comparison.CurvatureToENT
public import ENT.Small.FixedSupportKL
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! A lower curvature bound for uniform projections gives a quantitative entropy comparison. Subtracting a quartic term retains the KL remainder. -/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ENT.Quantitative
noncomputable section

theorem third_derivative_sub_quartic {V : ℝ → ℝ} {x : ℝ}
    (hV : ContDiffAt ℝ 3 V x) (c : ℝ) :
    deriv (deriv (deriv (fun y => V y - c * y ^ 4))) x =
      deriv (deriv (deriv V)) x - 24 * c * x := by
  have h := iteratedDeriv_fun_sub (n := 3) (g := fun y => c * y ^ 4) hV
    (contDiffAt_const.mul (contDiffAt_id.pow 4))
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow] at h
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero] at h
  convert h using 1 <;> ring

def quarticAdjustedPotential (n : ℕ) (b : ℝ) (x : ℝ) : ℝ :=
  Spline.diagonalSplinePotential n x - b / (24 * (n : ℝ)) * x ^ 4

theorem quarticAdjusted_curvaturePotential {n : ℕ} (hn : 5 ≤ n) (b : ℝ)
    (hcurv : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt n),
      (b / (n : ℝ)) * x ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x) :
    Comparison.CurvaturePotential (Real.sqrt n) (quarticAdjustedPotential n b) := by
  have hn0 : 0 < n := by omega
  have hR : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn0)
  have hsmooth (x : ℝ) (hx : x ∈ Ioo (-Real.sqrt n) (Real.sqrt n)) :
      ContDiffAt ℝ 3 (Spline.diagonalSplinePotential n) x :=
    Spline.contDiffAt_diagonalSplinePotential 3 n (by omega) x
      (ne_of_gt (Spline.diagonalSplineDensity_pos n (by omega) x hx))
  have hW (x : ℝ) (hx : x ∈ Ioo (-Real.sqrt n) (Real.sqrt n)) :
      ContDiffAt ℝ 3 (quarticAdjustedPotential n b) x :=
    (hsmooth x hx).sub (contDiffAt_const.mul (contDiffAt_id.pow 4))
  have hpositive (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (Real.sqrt n)) :
      0 ≤ deriv (deriv (deriv (quarticAdjustedPotential n b))) x := by
    change 0 ≤ deriv (deriv (deriv (fun y => Spline.diagonalSplinePotential n y -
      b / (24 * (n : ℝ)) * y ^ 4))) x
    rw [third_derivative_sub_quartic
      (hsmooth x ⟨by linarith [hx.1], hx.2⟩)]
    have hc : 24 * (b / (24 * (n : ℝ))) = b / (n : ℝ) := by ring
    rw [hc]
    exact sub_nonneg.mpr (hcurv x hx)
  refine ⟨hR, ?_, ?_, hW, ?_⟩
  · exact ((Spline.continuous_diagonalSplineDensity n).measurable.log.neg).sub
      (measurable_const.mul (measurable_id.pow_const 4))
  · intro x
    unfold quarticAdjustedPotential Spline.diagonalSplinePotential
    rw [Spline.diagonalSplineDensity_even n (by omega)]
    ring
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with hzero | hpositiveX
    · subst x
      have h0 := hW 0 ⟨by linarith, hR⟩
      have h1 : ContDiffAt ℝ 2 (deriv (quarticAdjustedPotential n b)) 0 :=
        h0.derivWithin (by norm_num)
      have h2 : ContDiffAt ℝ 1 (deriv (deriv (quarticAdjustedPotential n b))) 0 :=
        h1.derivWithin (by norm_num)
      have h3 : ContDiffAt ℝ 0
          (deriv (deriv (deriv (quarticAdjustedPotential n b)))) 0 :=
        h2.derivWithin (by norm_num)
      exact Comparison.nonneg_at_zero_of_positive_half hR h3.continuousAt hpositive
    · exact hpositive x ⟨hpositiveX, hx.2⟩

theorem curvature_potential_gap {n : ℕ} (hn : 5 ≤ n) (b : ℝ)
    (hcurv : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt n),
      (b / (n : ℝ)) * x ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    b * deficit a / (180 * (n : ℝ)) ≤
      (∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw (diagonal n)) -
      (∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw a) := by
  let J := quarticAdjusted_curvaturePotential hn b hcurv
  have hq : Integrable (Spline.diagonalSplinePotential n) (projectionLaw (diagonal n)) :=
    Spline.diagonalSplinePotential_integrable n (by omega)
  have hp : Integrable (Spline.diagonalSplinePotential n) (projectionLaw a) :=
    Small.integrable_potential_of_finiteKL
      (Small.unitProjectionFiniteKLData (by omega) a ha (projectionFiniteEntropyDensity a ha))
  have h4p := integrable_projectionLaw_pow a 4
  have h4q := integrable_projectionLaw_pow (diagonal n) 4
  have hW : Integrable (quarticAdjustedPotential n b) (projectionLaw (diagonal n)) :=
    hq.sub (h4q.const_mul (b / (24 * (n : ℝ))))
  have he := J.expectation_le (by omega)
    (Spline.ae_mem_diagonalSplineSupport n (by omega)) hW a ha
  change (∫ x, Spline.diagonalSplinePotential n x -
      b / (24 * (n : ℝ)) * x ^ 4 ∂projectionLaw a) ≤
    (∫ x, Spline.diagonalSplinePotential n x -
      b / (24 * (n : ℝ)) * x ^ 4 ∂projectionLaw (diagonal n)) at he
  rw [integral_sub hp (h4p.const_mul _), integral_sub hq (h4q.const_mul _),
    integral_const_mul, integral_const_mul] at he
  calc
    b * deficit a / (180 * (n : ℝ)) =
        (b / (24 * (n : ℝ))) * ((∫ x, x ^ 4 ∂projectionLaw (diagonal n)) -
          (∫ x, x ^ 4 ∂projectionLaw a)) := by
      rw [diagonal_fourth_moment_gap (by omega) a ha]
      ring
    _ ≤ _ := by linarith

/-- The quantitative criterion, with the finite KL divergence retained.
The curvature premise is explicit here and is discharged in applications. -/
theorem curvature_entropy_gap {n : ℕ} (hn : 5 ≤ n) (b : ℝ)
    (hcurv : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt n),
      (b / (n : ℝ)) * x ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x)
    (a : Fin n → ℝ) (ha : IsUnit a)
    (p : FiniteEntropyDensity (projectionLaw a)) :
    b * deficit a / (180 * (n : ℝ)) +
        (Small.unitProjectionFiniteKLData (by omega) a ha p).klDivergence ≤
      (Spline.diagonalFiniteEntropyDensity n (by omega)).entropy - p.entropy := by
  let h := Small.unitProjectionFiniteKLData (by omega : 2 ≤ n) a ha p
  rw [h.entropy_gap_identity, h.potential_gap_eq_law_integrals]
  simpa only [Spline.diagonalFiniteEntropyDensity_density,
    Spline.diagonalSplinePotential, add_comm] using
      add_le_add_right (curvature_potential_gap hn b hcurv a ha) h.klDivergence

end
end ENT.Quantitative
