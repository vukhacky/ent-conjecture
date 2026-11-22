module

public import ENT.Small.Quadrature
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The midpoint quadrature rule with error at most M(b − a)³/24 when the second derivative has absolute value at most M throughout [a, b]. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped Topology

namespace ENT.Integration
noncomputable section

theorem midpoint_linear_taylor_error {f : ℝ → ℝ} {a b M : ℝ}
    (hab : a < b) (hf : ContDiffOn ℝ 2 f (Icc a b))
    (hM : ∀ y ∈ Icc a b, |deriv (deriv f) y| ≤ M)
    (x : ℝ) (hx : x ∈ Icc a b) :
    |f x - (f ((a+b)/2) + deriv f ((a+b)/2) * (x - (a+b)/2))| ≤
      M * (x - (a+b)/2)^2 / 2 := by
  let m := (a+b)/2
  have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hmC : m ∈ Icc a b := ⟨hm.1.le,hm.2.le⟩
  change |f x - (f m + deriv f m * (x-m))| ≤ M*(x-m)^2/2
  by_cases hxm : x = m
  · simp only [hxm, sub_self, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, abs_zero, le_refl]
  · have hmx : m ≠ x := Ne.symm hxm
    have hsub : uIcc m x ⊆ Icc a b := uIcc_subset_Icc hmC hx
    obtain ⟨y,hy,heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (n := 1) hmx (hf.mono hsub)
    have hfm : DifferentiableAt ℝ f m :=
      (hf.contDiffAt (Icc_mem_nhds hm.1 hm.2)).differentiableAt (by norm_num)
    have hder : derivWithin f (uIcc m x) m = deriv f m :=
      hfm.derivWithin ((uniqueDiffOn_uIcc hmx) m left_mem_uIcc)
    have ht : taylorWithinEval f 1 (uIcc m x) m x = f m + deriv f m * (x-m) := by
      rw [show (1 : ℕ) = 0+1 from rfl, taylorWithinEval_succ]
      simp only [taylor_within_zero_eval, Nat.cast_zero, zero_add, Nat.factorial_zero,
        Nat.cast_one, one_mul, inv_one, pow_one, iteratedDerivWithin_one,
        smul_eq_mul, hder]
      ring
    rw [ht] at heq
    norm_num only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial,
      Nat.cast_ofNat, Nat.reduceAdd] at heq
    have hyC : y ∈ Icc a b := hsub ⟨hy.1.le,hy.2.le⟩
    rw [heq, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (x-m))]
    norm_num only
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hM y hyC) (sq_nonneg _)) (by norm_num)

theorem integral_midpoint_linear (f : ℝ → ℝ) (a b : ℝ) :
    (∫ x in a..b, f ((a+b)/2) + deriv f ((a+b)/2)*(x-(a+b)/2)) =
      (b-a)*f ((a+b)/2) := by
  have hi : IntervalIntegrable (fun x : ℝ => deriv f ((a+b)/2)*(x-(a+b)/2)) volume a b :=
    (by fun_prop : Continuous (fun x : ℝ => deriv f ((a+b)/2)*(x-(a+b)/2))).intervalIntegrable a b
  rw [intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) ((a+b)/2)]
  rw [show (fun x : ℝ => x) = (fun x => x^1) by funext x; simp,
    integral_pow]
  simp only [smul_eq_mul]
  norm_num only
  ring

theorem integral_midpoint_quadratic (a b M : ℝ) :
    (∫ x in a..b, M * (x-(a+b)/2)^2/2) = M*(b-a)^3/24 := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^2) ((a+b)/2), integral_pow]
  norm_num only
  ring

/-- Whole-cell smoothness and second-derivative control imply the exact
midpoint error bound `M * (b-a)^3 / 24`, including a degenerate cell. -/
theorem midpoint_error_bound {f : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hf : ContDiffOn ℝ 2 f (Icc a b))
    (hM : ∀ y ∈ Icc a b, |deriv (deriv f) y| ≤ M) :
    |(∫ x in a..b, f x) - (b-a)*f ((a+b)/2)| ≤ M*(b-a)^3/24 := by
  rcases eq_or_lt_of_le hab with rfl | hablt
  · simp
  · let L := fun x => f ((a+b)/2) + deriv f ((a+b)/2)*(x-(a+b)/2)
    have hfI : IntervalIntegrable f volume a b :=
      hf.continuousOn.intervalIntegrable_of_Icc hab
    have hLI : IntervalIntegrable L volume a b :=
      (by fun_prop : Continuous L).intervalIntegrable a b
    have hB : IntervalIntegrable (fun x : ℝ => M*(x-(a+b)/2)^2/2) volume a b :=
      (by fun_prop : Continuous (fun x : ℝ => M*(x-(a+b)/2)^2/2)).intervalIntegrable a b
    have hbound := intervalIntegral.norm_integral_le_of_norm_le (f := fun x => f x-L x)
      hab (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]
        exact midpoint_linear_taylor_error hablt hf hM x ⟨hx.1.le,hx.2⟩) hB
    rw [intervalIntegral.integral_sub hfI hLI, integral_midpoint_linear,
      integral_midpoint_quadratic, Real.norm_eq_abs] at hbound
    exact hbound

end
end ENT.Integration
