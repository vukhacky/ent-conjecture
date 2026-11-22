module

public import ENT.Base.TwoDensity
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Exact integration of the trapezoidal density, including the endpoint at density zero. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set

namespace ENT

noncomputable section

theorem integral_mul_log_from_zero {c : ℝ} (hc : 0 ≤ c) :
    (∫ x in 0..c, x * Real.log x) = c ^ 2 / 2 * Real.log c - c ^ 2 / 4 := by
  let P : ℝ → ℝ := fun x => x * (x * Real.log x) / 2 - x ^ 2 / 4
  have hcont : Continuous P := by
    dsimp [P]
    fun_prop
  have hderiv : ∀ x ∈ Ioo 0 c, HasDerivAt P (x * Real.log x) x := by
    intro x hx
    have hraw := (((hasDerivAt_id x).mul
      (Real.hasDerivAt_mul_log (ne_of_gt hx.1))).div_const 2).sub
      (((hasDerivAt_id x).pow 2).div_const 4)
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq] at hraw
    dsimp [P]
    convert hraw using 1
    ring
  calc
    _ = P c - P 0 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc
      hcont.continuousOn hderiv (Real.continuous_mul_log.intervalIntegrable 0 c)
    _ = _ := by
      simp only [P, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
      ring

theorem integral_scale_mul_log {k L : ℝ} (hk : 0 < k) (hL : 0 ≤ L) :
    (∫ x in 0..L, (k * x) * Real.log (k * x)) =
      k * L ^ 2 / 2 * Real.log (k * L) - k * L ^ 2 / 4 := by
  rw [intervalIntegral.integral_comp_mul_left (f := fun y : ℝ => y * Real.log y) hk.ne']
  rw [mul_zero, integral_mul_log_from_zero (mul_nonneg hk.le hL)]
  simp only [smul_eq_mul]
  field_simp [hk.ne']

theorem integral_even_of_bounded_support {f : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : Continuous f) (heven : ∀ x, f (-x) = f x)
    (hsupport : ∀ x, x ∉ Icc (-R) R → f x = 0) :
    (∫ x, f x) = 2 * ∫ x in 0..R, f x := by
  have hnegative : (∫ x in -R..0, f x) = ∫ x in 0..R, f x := by
    simpa only [heven, neg_zero, neg_neg] using
      (intervalIntegral.integral_comp_neg (f := f) (a := -R) (b := 0))
  calc
    _ = ∫ x in Icc (-R) R, f x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).symm
    _ = ∫ x in -R..R, f x := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
    _ = (∫ x in -R..0, f x) + ∫ x in 0..R, f x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable (-R) 0) (hf.intervalIntegrable 0 R)).symm
    _ = _ := by rw [hnegative]; ring

theorem entropy_twoDensity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) :
    -(∫ x, twoDensity a b x * Real.log (twoDensity a b x)) =
      Real.log (2 * a) + b / (2 * a) := by
  let f : ℝ → ℝ := fun x => twoDensity a b x * Real.log (twoDensity a b x)
  let k : ℝ := (2 * a)⁻¹ * (2 * b)⁻¹
  have hk : 0 < k := by dsimp [k]; positivity
  have hkedge : k * (2 * b) = (2 * a)⁻¹ := by
    dsimp [k]
    rw [mul_assoc, inv_mul_cancel₀ (by positivity : 2 * b ≠ 0), mul_one]
  have hf : Continuous f := Real.continuous_mul_log.comp (continuous_twoDensity a b)
  have hwhole : (∫ x, f x) = 2 * ∫ x in 0..a + b, f x := by
    apply integral_even_of_bounded_support (by positivity) hf
    · intro x
      simp only [f, twoDensity_neg]
    · intro x hx
      simp only [f, twoDensity_eq_zero_of_not_mem a b x hx, zero_mul]
  have hplateau : (∫ x in 0..a - b, f x) =
      (a - b) * ((2 * a)⁻¹ * Real.log ((2 * a)⁻¹)) := by
    calc
      _ = ∫ x in 0..a - b, (2 * a)⁻¹ * Real.log ((2 * a)⁻¹) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : 0 ≤ a - b)] at hx
        dsimp [f]
        rw [twoDensity_eq_const hb hab hx.1 hx.2]
      _ = _ := by simp; ring
  have htail : (∫ x in a - b..a + b, f x) =
      k * (2 * b) ^ 2 / 2 * Real.log (k * (2 * b)) - k * (2 * b) ^ 2 / 4 := by
    calc
      _ = ∫ x in a - b..a + b,
          (k * (a + b - x)) * Real.log (k * (a + b - x)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : a - b ≤ a + b)] at hx
        dsimp [f, k]
        rw [twoDensity_eq_slope hab hx.1 hx.2]
      _ = ∫ x in 0..2 * b, (k * x) * Real.log (k * x) := by
        have hsub := intervalIntegral.integral_comp_sub_left
          (f := fun y : ℝ => (k * y) * Real.log (k * y))
          (a := a - b) (b := a + b) (a + b)
        simpa only [show a + b - (a + b) = 0 by ring,
          show a + b - (a - b) = 2 * b by ring] using hsub
      _ = _ := integral_scale_mul_log hk (by positivity)
  change -(∫ x, f x) = _
  rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 (a - b)) (hf.intervalIntegrable (a - b) (a + b)),
    hplateau, htail, hkedge, Real.log_inv]
  dsimp [k]
  field_simp [ha.ne', hb.ne']
  ring

theorem twoFiniteEntropyDensity_entropy (a : Fin 2 → ℝ) (ha : 0 < a 0)
    (hb : 0 < a 1) (hab : a 1 ≤ a 0) :
    (twoFiniteEntropyDensity a ha hb).entropy =
      Real.log (2 * a 0) + a 1 / (2 * a 0) := by
  exact entropy_twoDensity ha hb hab

end
end ENT
