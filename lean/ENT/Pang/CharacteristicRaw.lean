module

public import ENT.Pang.MomentBounds
public import ENT.Pang.SineScalar

/-! Exact real characteristic integrals of the uncentered exponential tilt. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory
open scoped Interval

namespace ENT.Pang

noncomputable section

theorem integral_exp_cos (t s a b : ℝ) (hden : t ^ 2 + s ^ 2 ≠ 0) :
    (∫ x in a..b, Real.exp (t * x) * Real.cos (s * x)) =
      (Real.exp (t * b) * (t * Real.cos (s * b) + s * Real.sin (s * b)) -
        Real.exp (t * a) * (t * Real.cos (s * a) + s * Real.sin (s * a))) /
        (t ^ 2 + s ^ 2) := by
  have hd : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (t * y) *
        (t * Real.cos (s * y) + s * Real.sin (s * y)) / (t ^ 2 + s ^ 2))
        (Real.exp (t * x) * Real.cos (s * x)) x := by
    intro x
    have hc := (Real.hasDerivAt_cos (s * x)).comp x ((hasDerivAt_id x).const_mul s)
    have hs := (Real.hasDerivAt_sin (s * x)).comp x ((hasDerivAt_id x).const_mul s)
    have h := ((((hasDerivAt_id x).const_mul t).exp).mul
      ((hc.const_mul t).add (hs.const_mul s))).div_const (t ^ 2 + s ^ 2)
    apply h.congr_deriv
    simp only [id_eq, Function.comp_apply, Pi.add_apply]
    field_simp [hden]
    ring
  have hi : IntervalIntegrable
      (fun x : ℝ => Real.exp (t * x) * Real.cos (s * x)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi
  simpa only [sub_div] using h

theorem integral_exp_sin (t s a b : ℝ) (hden : t ^ 2 + s ^ 2 ≠ 0) :
    (∫ x in a..b, Real.exp (t * x) * Real.sin (s * x)) =
      (Real.exp (t * b) * (t * Real.sin (s * b) - s * Real.cos (s * b)) -
        Real.exp (t * a) * (t * Real.sin (s * a) - s * Real.cos (s * a))) /
        (t ^ 2 + s ^ 2) := by
  have hd : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (t * y) *
        (t * Real.sin (s * y) - s * Real.cos (s * y)) / (t ^ 2 + s ^ 2))
        (Real.exp (t * x) * Real.sin (s * x)) x := by
    intro x
    have hc := (Real.hasDerivAt_cos (s * x)).comp x ((hasDerivAt_id x).const_mul s)
    have hs := (Real.hasDerivAt_sin (s * x)).comp x ((hasDerivAt_id x).const_mul s)
    have h := ((((hasDerivAt_id x).const_mul t).exp).mul
      ((hs.const_mul t).sub (hc.const_mul s))).div_const (t ^ 2 + s ^ 2)
    apply h.congr_deriv
    simp only [id_eq, Function.comp_apply, Pi.sub_apply]
    field_simp [hden]
    ring
  have hi : IntervalIntegrable
      (fun x : ℝ => Real.exp (t * x) * Real.sin (s * x)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi
  simpa only [sub_div] using h

def tiltCos (t s : ℝ) : ℝ := ∫ x, Real.cos (s * x) ∂tiltLaw t
def tiltSin (t s : ℝ) : ℝ := ∫ x, Real.sin (s * x) ∂tiltLaw t

theorem tiltCos_eq {t : ℝ} (ht : 0 < t) (s : ℝ) :
    tiltCos t s = t / (t ^ 2 + s ^ 2) *
      (t * Real.cos s + s * (Real.cosh t / Real.sinh t) * Real.sin s) := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have hden : t ^ 2 + s ^ 2 ≠ 0 := (by positivity : 0 < t ^ 2 + s ^ 2).ne'
  unfold tiltCos
  rw [integral_tiltLaw ht]
  have heq : (fun x : ℝ => Real.cos (s * x) * tiltWeight t x) =
      (fun x : ℝ => t / (2 * Real.sinh t) *
        (Real.exp (t * x) * Real.cos (s * x))) := by
    funext x
    unfold tiltWeight
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_exp_cos t s (-1) 1 hden]
  simp only [mul_one, mul_neg_one, Real.cos_neg, Real.sin_neg]
  rw [← Real.cosh_add_sinh t, ← Real.cosh_sub_sinh t]
  field_simp [hs, hden]
  ring

theorem tiltSin_eq {t : ℝ} (ht : 0 < t) (s : ℝ) :
    tiltSin t s = t / (t ^ 2 + s ^ 2) *
      (t * (Real.cosh t / Real.sinh t) * Real.sin s - s * Real.cos s) := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have hden : t ^ 2 + s ^ 2 ≠ 0 := (by positivity : 0 < t ^ 2 + s ^ 2).ne'
  unfold tiltSin
  rw [integral_tiltLaw ht]
  have heq : (fun x : ℝ => Real.sin (s * x) * tiltWeight t x) =
      (fun x : ℝ => t / (2 * Real.sinh t) *
        (Real.exp (t * x) * Real.sin (s * x))) := by
    funext x
    unfold tiltWeight
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_exp_sin t s (-1) 1 hden]
  simp only [mul_one, mul_neg_one, Real.cos_neg, Real.sin_neg]
  rw [← Real.cosh_add_sinh t, ← Real.cosh_sub_sinh t]
  field_simp [hs, hden]
  ring

theorem tiltTrig_sq_eq {t : ℝ} (ht : 0 < t) (s : ℝ) :
    tiltCos t s ^ 2 + tiltSin t s ^ 2 =
      t ^ 2 / (t ^ 2 + s ^ 2) * (1 + Real.sin s ^ 2 / Real.sinh t ^ 2) := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have hden : t ^ 2 + s ^ 2 ≠ 0 := (by positivity : 0 < t ^ 2 + s ^ 2).ne'
  rw [tiltCos_eq ht, tiltSin_eq ht]
  field_simp [hs, hden]
  ring_nf
  simp only [Real.cosh_sq, Real.cos_sq']
  ring

theorem tiltTrig_sq_pos {t : ℝ} (ht : 0 < t) (s : ℝ) :
    0 < tiltCos t s ^ 2 + tiltSin t s ^ 2 := by
  rw [tiltTrig_sq_eq ht]
  positivity

theorem tiltTrig_weighted_sq_le {t : ℝ} (ht : 0 < t) (s : ℝ) :
    (1 + s ^ 2 * tiltVariance t) * (tiltCos t s ^ 2 + tiltSin t s ^ 2) ≤ 1 := by
  have hv := (tiltVariance_lt_one_third ht).le
  have hsin := sine_variance_envelope s (tiltVariance t) hv
  have haux : (1 + s ^ 2 * tiltVariance t) *
      (1 + Real.sin s ^ 2 / Real.sinh t ^ 2) ≤ 1 + s ^ 2 / t ^ 2 := by
    calc
      _ = (1 + s ^ 2 * tiltVariance t) +
          ((1 + s ^ 2 * tiltVariance t) * Real.sin s ^ 2) / Real.sinh t ^ 2 := by ring
      _ ≤ (1 + s ^ 2 * tiltVariance t) + s ^ 2 / Real.sinh t ^ 2 := by
        linarith only [div_le_div_of_nonneg_right hsin (sq_nonneg (Real.sinh t))]
      _ = 1 + s ^ 2 / t ^ 2 := by unfold tiltVariance; ring
  have hden : t ^ 2 + s ^ 2 ≠ 0 := (by positivity : 0 < t ^ 2 + s ^ 2).ne'
  rw [tiltTrig_sq_eq ht]
  calc
    _ = (t ^ 2 / (t ^ 2 + s ^ 2)) * ((1 + s ^ 2 * tiltVariance t) *
        (1 + Real.sin s ^ 2 / Real.sinh t ^ 2)) := by ring
    _ ≤ (t ^ 2 / (t ^ 2 + s ^ 2)) * (1 + s ^ 2 / t ^ 2) :=
      mul_le_mul_of_nonneg_left haux (by positivity)
    _ = 1 := by field_simp [ht.ne', hden]

theorem tiltTrig_sq_le {t : ℝ} (ht : 0 < t) (s : ℝ) :
    tiltCos t s ^ 2 + tiltSin t s ^ 2 ≤ 1 / (1 + s ^ 2 * tiltVariance t) := by
  have hv : 0 < tiltVariance t := tiltVariance_pos ht
  apply (le_div_iff₀ (by positivity : 0 < 1 + s ^ 2 * tiltVariance t)).mpr
  simpa only [mul_comm] using tiltTrig_weighted_sq_le ht s

end
end ENT.Pang
