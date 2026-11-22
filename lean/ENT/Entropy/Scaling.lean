module

public import ENT.Entropy.LawInvariance
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! Positive scaling of an actual finite-entropy density. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT

noncomputable section

def scaledDensity (c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := c⁻¹ * f (x / c)

theorem scaledDensity_mul_log {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) (x : ℝ) :
    scaledDensity c f x * Real.log (scaledDensity c f x) =
      c⁻¹ * (f (x / c) * Real.log (f (x / c)) - Real.log c * f (x / c)) := by
  unfold scaledDensity
  by_cases hf : f (x / c) = 0
  · simp [hf]
  · rw [Real.log_mul (inv_ne_zero hc.ne') hf, Real.log_inv]
    ring

def inverseDilation (c : ℝ) (hc : 0 < c) : ℝ ≃ᵐ ℝ where
  toFun x := x / c
  invFun x := c * x
  left_inv x := by field_simp
  right_inv x := by field_simp
  measurable_toFun := by change Measurable (fun x : ℝ => x / c); fun_prop
  measurable_invFun := by change Measurable (fun x : ℝ => c * x); fun_prop

theorem inverseDilation_hasDerivAt (c : ℝ) (hc : 0 < c) (x : ℝ) :
    HasDerivAt (inverseDilation c hc) c⁻¹ x := by
  change HasDerivAt (fun x : ℝ => x / c) c⁻¹ x
  simpa only [one_div, id_eq] using (hasDerivAt_id x).div_const c

namespace FiniteEntropyDensity

variable {μ : Measure ℝ}

theorem integrable_scaledDensity (p : FiniteEntropyDensity μ) {c : ℝ} (hc : 0 < c) :
    Integrable (scaledDensity c p.density) :=
  (p.integrable.comp_div hc.ne').const_mul c⁻¹

theorem integral_scaledDensity (p : FiniteEntropyDensity μ) {c : ℝ} (hc : 0 < c) :
    (∫ x, scaledDensity c p.density x) = 1 := by
  change (∫ x, c⁻¹ * p.density (x / c)) = 1
  rw [integral_const_mul, Measure.integral_comp_div,
    abs_of_pos hc, smul_eq_mul, p.mass_one, mul_one, inv_mul_cancel₀ hc.ne']

theorem integrable_scaledDensity_mul_log (p : FiniteEntropyDensity μ)
    {c : ℝ} (hc : 0 < c) :
    Integrable (fun x => scaledDensity c p.density x * Real.log (scaledDensity c p.density x)) := by
  simp_rw [scaledDensity_mul_log hc]
  exact ((p.entropy_integrable.comp_div hc.ne').sub'
    ((p.integrable.comp_div hc.ne').const_mul (Real.log c))).const_mul c⁻¹

theorem scaledDensity_law (p : FiniteEntropyDensity μ) {c : ℝ} (hc : 0 < c) :
    μ.map (fun x => c * x) = volume.withDensity (fun x => ENNReal.ofReal (scaledDensity c p.density x)) := by
  let e := inverseDilation c hc
  conv_lhs => rw [p.law_eq]
  change (volume.withDensity (fun x => ENNReal.ofReal (p.density x))).map e.symm = _
  apply Measure.ext
  intro s hs
  rw [e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs
    (inverseDilation_hasDerivAt c hc) (Filter.Eventually.of_forall p.nonneg) p.integrable]
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal (p.integrable_scaledDensity hc).integrableOn
      (Filter.Eventually.of_forall (fun x => mul_nonneg (inv_nonneg.mpr hc.le) (p.nonneg (x / c))))]
  congr 1
  apply setIntegral_congr_fun hs
  intro x hx
  rw [abs_of_pos (inv_pos.mpr hc)]
  rfl

def scale (p : FiniteEntropyDensity μ) (c : ℝ) (hc : 0 < c) :
    FiniteEntropyDensity (μ.map (fun x => c * x)) where
  density := scaledDensity c p.density
  nonneg x := mul_nonneg (inv_nonneg.mpr hc.le) (p.nonneg (x / c))
  measurable := measurable_const.mul (p.measurable.comp (by fun_prop))
  integrable := p.integrable_scaledDensity hc
  mass_one := p.integral_scaledDensity hc
  law_eq := p.scaledDensity_law hc
  entropy_integrable := p.integrable_scaledDensity_mul_log hc

@[simp]
theorem scale_density (p : FiniteEntropyDensity μ) (c : ℝ) (hc : 0 < c) :
    (p.scale c hc).density = scaledDensity c p.density := rfl

theorem entropy_scale (p : FiniteEntropyDensity μ) (c : ℝ) (hc : 0 < c) :
    (p.scale c hc).entropy = p.entropy + Real.log c := by
  unfold entropy
  simp only [scale_density]
  simp_rw [scaledDensity_mul_log hc]
  have he : (∫ x, p.density (x / c) * Real.log (p.density (x / c))) =
      c * ∫ x, p.density x * Real.log (p.density x) := by
    simpa only [abs_of_pos hc, smul_eq_mul] using
      Measure.integral_comp_div (fun x => p.density x * Real.log (p.density x)) c
  rw [integral_const_mul,
    integral_sub (p.entropy_integrable.comp_div hc.ne')
      ((p.integrable.comp_div hc.ne').const_mul (Real.log c)),
    integral_const_mul, he, Measure.integral_comp_div,
    abs_of_pos hc, smul_eq_mul, p.mass_one]
  field_simp
  ring

end FiniteEntropyDensity

end
end ENT
