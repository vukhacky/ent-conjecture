module

public import ENT.Pang.SineConvex
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Elementary polar identities and angle bounds used in the local estimates. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Pang

noncomputable section

theorem complex_pow_polar (z : ℂ) (n : ℕ) :
    (z ^ n).re = ‖z‖ ^ n * Real.cos ((n : ℝ) * z.arg) ∧
      (z ^ n).im = ‖z‖ ^ n * Real.sin ((n : ℝ) * z.arg) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Complex.mul_re, Complex.mul_im, ih.1, ih.2]
    have hre := Complex.norm_mul_cos_arg z
    have him := Complex.norm_mul_sin_arg z
    rw [← hre, ← him]
    push_cast
    rw [add_mul, one_mul, Real.cos_add, Real.sin_add, pow_succ]
    constructor <;> ring

theorem complex_arg_le_im_div_re {z : ℂ} (hre : 0 < z.re) (him : 0 ≤ z.im) :
    z.arg ≤ z.im / z.re := by
  have hlo : -(Real.pi / 2) < z.arg := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hre)
  have hhi : z.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have har : z.arg = Real.arctan (z.im / z.re) := by
    rw [← Complex.tan_arg, Real.arctan_tan hlo hhi]
  rw [har]
  exact Real.arctan_le_self (div_nonneg him hre.le)

theorem complex_im_le_arg {z : ℂ} (him : 0 ≤ z.im) (hnorm : ‖z‖ ≤ 1) :
    z.im ≤ z.arg := by
  have ha : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr him
  have h := mul_le_mul_of_nonneg_left (Real.sin_le ha) (norm_nonneg z)
  rw [Complex.norm_mul_sin_arg] at h
  have hn := mul_le_mul_of_nonneg_right hnorm ha
  nlinarith

end
end ENT.Pang
