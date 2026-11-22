module

public import ENT.Spline.DiagonalProperties
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Tactic.FunProp

/-! Change of variables from a unit-sum density to the standardized density. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ENT.Spline

noncomputable section

def standardizationEquiv (n : ℕ) (hn : 0 < n) : ℝ ≃ᵐ ℝ where
  toFun x := ((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2
  invFun t := ((n : ℝ) - 2 * t) / Real.sqrt (n : ℝ)
  left_inv x := by
    have hr : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hn)
    field_simp
    <;> ring
  right_inv t := by
    have hr : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hn)
    field_simp
    <;> ring
  measurable_toFun := by
    change Measurable (fun x : ℝ => ((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2)
    fun_prop
  measurable_invFun := by
    change Measurable (fun t : ℝ => ((n : ℝ) - 2 * t) / Real.sqrt (n : ℝ))
    fun_prop

theorem standardizationEquiv_hasDerivAt (n : ℕ) (hn : 0 < n) (x : ℝ) :
    HasDerivAt (standardizationEquiv n hn) (-(Real.sqrt (n : ℝ)) / 2) x := by
  convert (((hasDerivAt_id x).const_mul (Real.sqrt (n : ℝ))).const_sub (n : ℝ)).div_const 2 using 1
  · rfl
  · ring

theorem map_unitSumSplineDensity_standardization (n : ℕ) (hn : 2 ≤ n) :
    (volume.withDensity (fun t => ENNReal.ofReal (unitSumSplineDensity n t))).map
      (fun t => ((n : ℝ) - 2 * t) / Real.sqrt (n : ℝ)) =
      volume.withDensity (fun x => ENNReal.ofReal (diagonalSplineDensity n x)) := by
  have hn0 : 0 < n := by omega
  let e := standardizationEquiv n hn0
  change (volume.withDensity (fun t => ENNReal.ofReal (unitSumSplineDensity n t))).map e.symm = _
  apply Measure.ext
  intro s hs
  rw [e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs
    (fun x => standardizationEquiv_hasDerivAt n hn0 x)
    (Filter.Eventually.of_forall (unitSumSplineDensity_nonneg n hn))
    (integrable_unitSumSplineDensity n hn)]
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_diagonalSplineDensity n hn).integrableOn
      (Filter.Eventually.of_forall (diagonalSplineDensity_nonneg n hn))]
  congr 1
  apply setIntegral_congr_fun hs
  intro x hx
  change |-(Real.sqrt (n : ℝ)) / 2| * unitSumSplineDensity n
      (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2) = diagonalSplineDensity n x
  rw [abs_div, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rfl

end
end ENT.Spline
