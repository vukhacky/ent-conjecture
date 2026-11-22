module

public import ENT.Pang.HyperbolicPolynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The rational sine envelope for Pang’s characteristic-function bound follows from three derivative estimates and `sin² ≤ 1`. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Pang

noncomputable section

def cosFourthRemainder (x : ℝ) : ℝ := 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x
def sinFifthRemainder (x : ℝ) : ℝ := x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x
def cosSixthRemainder (x : ℝ) : ℝ :=
  Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)

theorem hasDerivAt_cosFourthRemainder (x : ℝ) :
    HasDerivAt cosFourthRemainder (-x + x ^ 3 / 6 + Real.sin x) x := by
  have h := (((hasDerivAt_const x (1 : ℝ)).sub
      (((hasDerivAt_id x).pow 2).div_const 2)).add
    (((hasDerivAt_id x).pow 4).div_const 24)).sub (Real.hasDerivAt_cos x)
  apply h.congr_deriv
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, id_eq]
  ring

theorem hasDerivAt_sinFifthRemainder (x : ℝ) :
    HasDerivAt sinFifthRemainder (cosFourthRemainder x) x := by
  have h := (((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 6)).add
    (((hasDerivAt_id x).pow 5).div_const 120)).sub (Real.hasDerivAt_sin x)
  apply h.congr_deriv
  unfold cosFourthRemainder
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, id_eq]
  ring

theorem hasDerivAt_cosSixthRemainder (x : ℝ) :
    HasDerivAt cosSixthRemainder (sinFifthRemainder x) x := by
  have h := (Real.hasDerivAt_cos x).sub
    ((((hasDerivAt_const x (1 : ℝ)).sub (((hasDerivAt_id x).pow 2).div_const 2)).add
      (((hasDerivAt_id x).pow 4).div_const 24)).sub
      (((hasDerivAt_id x).pow 6).div_const 720))
  apply h.congr_deriv
  unfold sinFifthRemainder
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, id_eq]
  ring

theorem cosFourthRemainder_pos {x : ℝ} (hx : 0 < x) : 0 < cosFourthRemainder x := by
  apply positive_of_positive_derivative hasDerivAt_cosFourthRemainder
    (by norm_num [cosFourthRemainder]) ?_ hx
  intro y hy
  nlinarith [Real.sin_gt_sub_cube hy]

theorem sinFifthRemainder_pos {x : ℝ} (hx : 0 < x) : 0 < sinFifthRemainder x :=
  positive_of_positive_derivative hasDerivAt_sinFifthRemainder
    (by norm_num [sinFifthRemainder]) (fun _ hy => cosFourthRemainder_pos hy) hx

theorem cosSixthRemainder_pos {x : ℝ} (hx : 0 < x) : 0 < cosSixthRemainder x :=
  positive_of_positive_derivative hasDerivAt_cosSixthRemainder
    (by norm_num [cosSixthRemainder]) (fun _ hy => sinFifthRemainder_pos hy) hx

theorem cos_lower_six_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  obtain rfl | hx := hx.eq_or_lt
  · norm_num
  · have h := cosSixthRemainder_pos hx
    unfold cosSixthRemainder at h
    linarith

theorem cos_lower_six (x : ℝ) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  rcases le_total 0 x with hx | hx
  · exact cos_lower_six_nonneg hx
  · have h := cos_lower_six_nonneg (neg_nonneg.mpr hx)
    rw [show (-x) ^ 2 = x ^ 2 by ring, show (-x) ^ 4 = x ^ 4 by ring,
      show (-x) ^ 6 = x ^ 6 by ring, Real.cos_neg] at h
    exact h

theorem sin_sq_upper_six (x : ℝ) :
    Real.sin x ^ 2 ≤ x ^ 2 - x ^ 4 / 3 + 2 * x ^ 6 / 45 := by
  have h := cos_lower_six (2 * x)
  rw [Real.cos_two_mul_eq_one_sub] at h
  nlinarith

/-- The scalar inequality required for every real frequency in Pang Lemma 4.2. -/
theorem sine_rational_envelope (x : ℝ) :
    (1 + x ^ 2 / 3) * Real.sin x ^ 2 ≤ x ^ 2 := by
  have hf : 0 ≤ 1 + x ^ 2 / 3 := by positivity
  by_cases hx : x ^ 2 ≤ 3 / 2
  · have h := mul_le_mul_of_nonneg_left (sin_sq_upper_six x) hf
    have hp : 0 ≤ x ^ 6 * (9 - 2 * x ^ 2) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith
  · have h := mul_le_mul_of_nonneg_left (Real.sin_sq_le_one x) hf
    linarith

theorem sine_variance_envelope (x v : ℝ) (hv : v ≤ 1 / 3) :
    (1 + x ^ 2 * v) * Real.sin x ^ 2 ≤ x ^ 2 := by
  have h := sine_rational_envelope x
  have hm := mul_le_mul_of_nonneg_left hv (sq_nonneg x)
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg (Real.sin x))
  nlinarith

end
end ENT.Pang
