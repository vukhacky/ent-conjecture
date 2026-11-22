module

public import ENT.Base.TwoEntropy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact mass and second moment of the continuous two-uniform convolution
density, evaluated using the piecewise polynomial formula and FTC. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped Interval

namespace ENT.Comparison
noncomputable section

theorem integral_twoDensity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x, twoDensity a b x) = 1 :=
  (twoFiniteEntropyDensity ![a, b] ha hb).mass_one

theorem integrable_mul_twoDensity {a b : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-(a + b)) (a + b))) :
    Integrable (fun x => g x * twoDensity a b x) volume := by
  have hi : IntegrableOn (fun x => g x * twoDensity a b x)
      (Icc (-(a + b)) (a + b)) volume :=
    (hg.mul (continuous_twoDensity a b).continuousOn).integrableOn_Icc
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [twoDensity_eq_zero_of_not_mem a b x hx, mul_zero]

theorem integral_twoDensity_second {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ a) :
    (∫ x, x ^ 2 * twoDensity a b x) = (a ^ 2 + b ^ 2) / 3 := by
  let f : ℝ → ℝ := fun x => x ^ 2 * twoDensity a b x
  let k : ℝ := (2 * a)⁻¹ * (2 * b)⁻¹
  have hf : Continuous f := (continuous_id.pow 2).mul (continuous_twoDensity a b)
  have hwhole : (∫ x, f x) = 2 * ∫ x in 0..a + b, f x := by
    apply ENT.integral_even_of_bounded_support (by positivity) hf
    · intro x
      simp only [f, neg_sq, twoDensity_neg]
    · intro x hx
      simp only [f, twoDensity_eq_zero_of_not_mem a b x hx, mul_zero]
  have hplateau : (∫ x in 0..a - b, f x) = (2 * a)⁻¹ * (a - b) ^ 3 / 3 := by
    calc
      _ = ∫ x in 0..a - b, (2 * a)⁻¹ * x ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : 0 ≤ a - b)] at hx
        dsimp [f]
        rw [twoDensity_eq_const hb hab hx.1 hx.2, mul_comm]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        norm_num
        ring
  have htail : (∫ x in a - b..a + b, f x) =
      k * ((a + b) * (a + b) ^ 3 / 3 - (a + b) ^ 4 / 4) -
      k * ((a + b) * (a - b) ^ 3 / 3 - (a - b) ^ 4 / 4) := by
    calc
      _ = ∫ x in a - b..a + b, k * ((a + b) * x ^ 2 - x ^ 3) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : a - b ≤ a + b)] at hx
        dsimp [f, k]
        rw [twoDensity_eq_slope hab hx.1 hx.2]
        ring
      _ = _ := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun x => k * ((a + b) * x ^ 3 / 3 - x ^ 4 / 4))
        · intro x _hx
          convert (((((hasDerivAt_pow 3 x).const_mul (a + b)).div_const 3).sub
            ((hasDerivAt_pow 4 x).div_const 4)).const_mul k) using 1; ring
        · apply Continuous.intervalIntegrable
          fun_prop
  change (∫ x, f x) = _
  rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 (a - b)) (hf.intervalIntegrable (a - b) (a + b)),
    hplateau, htail]
  dsimp [k]
  field_simp [ha.ne', hb.ne']
  ring

end
end ENT.Comparison
