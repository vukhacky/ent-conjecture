module

public import ENT.Small.Enclosures
public import ENT.Certificate.DenseDerivative
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Sound finite Taylor quadrature and exact integer-polynomial primitives. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Small

noncomputable section

theorem integral_enclosure_of_uniform_error {f p : ℝ → ℝ} {a b ε s : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hp : IntervalIntegrable p volume a b) (herror : ∀ x ∈ Icc a b, |f x - p x| ≤ ε)
    (hs : (∫ x in a..b, p x) = s) :
    s - (b - a) * ε ≤ (∫ x in a..b, f x) ∧
      (∫ x in a..b, f x) ≤ s + (b - a) * ε := by
  have hc : IntervalIntegrable (fun _ : ℝ => ε) volume a b := intervalIntegrable_const
  have hl := intervalIntegral.integral_mono_on hab (hp.sub hc) hf
    (fun x hx => by have h := (abs_le.mp (herror x hx)).1; linarith)
  have hu := intervalIntegral.integral_mono_on hab hf (hp.add hc)
    (fun x hx => by have h := (abs_le.mp (herror x hx)).2; linarith)
  rw [intervalIntegral.integral_sub hp hc, hs, intervalIntegral.integral_const,
    smul_eq_mul] at hl
  rw [intervalIntegral.integral_add hp hc, hs, intervalIntegral.integral_const,
    smul_eq_mul] at hu
  exact ⟨hl, hu⟩

theorem continuous_expTaylor (n : ℕ) : Continuous (Enclosures.expTaylor n) := by
  unfold Enclosures.expTaylor
  fun_prop

/-- The polynomial is formed in the exponent. Its integral is exact; only
the finite scalar Taylor remainder and a scalar exponential need enclosure. -/
theorem exp_cell_integral_enclosure {W : ℝ → ℝ} (hW : Continuous W)
    {n : ℕ} (hn : 0 < n) {a b c r l u s : ℝ} (hab : a ≤ b)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hlocal : ∀ x ∈ Icc a b, |c - W x| ≤ r)
    (hcoeff : l ≤ Real.exp (-c) ∧ Real.exp (-c) ≤ u)
    (hs : (∫ x in a..b, Enclosures.expTaylor n (c - W x)) = s)
    (hsl : 0 ≤ s - (b - a) * Enclosures.expError n r) :
    l * (s - (b - a) * Enclosures.expError n r) ≤
      (∫ x in a..b, Real.exp (-W x)) ∧
      (∫ x in a..b, Real.exp (-W x)) ≤
        u * (s + (b - a) * Enclosures.expError n r) := by
  have hf : Continuous (fun x => Real.exp (c - W x)) := (continuous_const.sub hW).rexp
  have hp : Continuous (fun x => Enclosures.expTaylor n (c - W x)) :=
    (continuous_expTaylor n).comp (continuous_const.sub hW)
  have h := integral_enclosure_of_uniform_error hab (hf.intervalIntegrable a b) (hp.intervalIntegrable a b)
    (fun x hx => Enclosures.exp_taylor_error hn hr0 hr1 (hlocal x hx)) hs
  have hi0 : 0 ≤ ∫ x in a..b, Real.exp (c - W x) :=
    intervalIntegral.integral_nonneg hab (fun x _ => (Real.exp_pos _).le)
  have he : (fun x => Real.exp (-W x)) =
      (fun x => Real.exp (-c) * Real.exp (c - W x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, intervalIntegral.integral_const_mul]
  constructor
  · exact mul_le_mul hcoeff.1 h.1 hsl (Real.exp_pos _).le
  · exact mul_le_mul hcoeff.2 h.2 hi0 ((Real.exp_pos _).le.trans hcoeff.2)

theorem exp_tail_integral_le {W : ℝ → ℝ} {R m : ℝ} (hm : 0 < m)
    (hi : Integrable (fun x => Real.exp (-W x)))
    (htangent : ∀ x ∈ Ici R, W R + m * (x - R) ≤ W x) :
    (∫ x in Ioi R, Real.exp (-W x)) ≤ Real.exp (-W R) / m := by
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-W R + m * R) * Real.exp (-m * x)) (Ioi R) :=
    (integrableOn_exp_mul_Ioi (by linarith : -m < 0) R).const_mul _
  have h := setIntegral_mono_on hi.integrableOn hg measurableSet_Ioi (fun x hx => by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := htangent x hx.le
    linarith)
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -m < 0)] at h
  have he : Real.exp (-W R + m * R) * (-Real.exp (-m * R) / -m) =
      Real.exp (-W R) / m := by
    rw [neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add]
    congr 2
    ring
  rwa [he] at h

theorem continuous_dense_eval (p : Certificate.IntPoly) : Continuous (Certificate.eval p) :=
  continuous_iff_continuousAt.mpr (fun x => (Certificate.Dense.hasDerivAt_eval p x).continuousAt)

theorem integral_dense_of_primitive {p F : Certificate.IntPoly} {D : ℤ}
    (hD : D ≠ 0) (hderiv : Certificate.Dense.derivative F = Certificate.Dense.scale D p)
    (a b : ℝ) :
    (∫ x in a..b, Certificate.eval p x) =
      (Certificate.eval F b - Certificate.eval F a) / (D : ℝ) := by
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hd (x : ℝ) : HasDerivAt (fun y => Certificate.eval F y / (D : ℝ))
      (Certificate.eval p x) x := by
    have h := (Certificate.Dense.hasDerivAt_eval F x).div_const (D : ℝ)
    rw [hderiv, Certificate.Dense.eval_scale] at h
    simpa only [mul_div_cancel_left₀ _ hDR] using h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) ((continuous_dense_eval p).intervalIntegrable a b)
  convert h using 1
  ring

end
end ENT.Small
