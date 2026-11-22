module

public import ENT.Quantitative.LangevinSharp
public import ENT.Pang.VarianceBounds
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Sharpness at zero tilt via differentiated genuine interval moments. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology Interval
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

theorem hasDerivAt_exponentialMoment_zero (k : ℕ) :
    HasDerivAt (fun t : ℝ=>exponentialMoment t k) (exponentialMoment 0 (k+1)) 0 := by
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun t x : ℝ=>x^k*Real.exp (t*x))
    (F':=fun t x : ℝ=>x^(k+1)*Real.exp (t*x))
    (x₀:=(0:ℝ)) (s:=Ioo (-1:ℝ) 1) (bound:=fun _ : ℝ=>Real.exp 1)
    (μ:=volume) (a:=(-1:ℝ)) (b:=1)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall (fun t=>(show Continuous (fun x : ℝ=>x^k*Real.exp (t*x)) by
      fun_prop).aestronglyMeasurable))
    (intervalIntegrable_exponentialMoment 0 k)
    ((show Continuous (fun x : ℝ=>x^(k+1)*Real.exp (0*x)) by fun_prop).aestronglyMeasurable)
    (Eventually.of_forall (fun x hx t ht=>by
      have hx' : x∈Ioc (-1:ℝ) 1 := by
        simpa only [uIoc_of_le (show (-1:ℝ)≤1 by norm_num)] using hx
      have hxt : |x|≤1 := abs_le.mpr ⟨hx'.1.le,hx'.2⟩
      have htt : |t|≤1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
      have htx : t*x≤1 := by
        calc
          t*x≤|t*x| := le_abs_self _
          _=|t| * |x| := abs_mul _ _
          _≤1*1 := mul_le_mul htt hxt (abs_nonneg _) (by norm_num)
          _=1 := by norm_num
      have hpow : ‖x^(k+1)‖≤1 := by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg x) (by simpa only [Real.norm_eq_abs] using hxt)
      calc
        ‖x^(k+1)*Real.exp (t*x)‖ = ‖x^(k+1)‖*Real.exp (t*x) := by
          simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _≤1*Real.exp 1 := mul_le_mul hpow (Real.exp_le_exp.mpr htx) (Real.exp_pos _).le (by norm_num)
        _=Real.exp 1 := one_mul _))
    intervalIntegrable_const
    (Eventually.of_forall (fun x _ t _=>by
      have hd := (((hasDerivAt_id t).mul_const x).exp).const_mul (x^k)
      apply hd.congr_deriv
      simp only [id_eq, one_mul, pow_succ]
      ring))
  exact h.2

/-- The normalized moment extends through zero without the removable singularity
of the hyperbolic expression used on the positive tilt axis. -/
def regularTiltMoment (t : ℝ) (k : ℕ) : ℝ :=
  exponentialMoment t k/exponentialMoment t 0

theorem regularTiltMoment_at_zero (k : ℕ) :
    regularTiltMoment 0 k = (1-(-1:ℝ)^(k+1))/(2*(k+1:ℝ)) := by
  unfold regularTiltMoment
  rw [exponentialMoment_at_zero, exponentialMoment_at_zero]
  norm_num
  field_simp

theorem hasDerivAt_regularTiltMoment_zero (k : ℕ) :
    HasDerivAt (fun t : ℝ=>regularTiltMoment t k) (exponentialMoment 0 (k+1)/2) 0 := by
  have he0 : exponentialMoment 0 0=2 := by norm_num [exponentialMoment_at_zero]
  have he1 : exponentialMoment 0 1=0 := by norm_num [exponentialMoment_at_zero]
  have h := (hasDerivAt_exponentialMoment_zero k).div (hasDerivAt_exponentialMoment_zero 0)
    (show exponentialMoment 0 0≠0 by rw [he0]; norm_num)
  apply h.congr_deriv
  rw [he0,he1]
  ring

theorem regularTiltMoment_eq {t : ℝ} (ht : 0<t) (k : ℕ) :
    regularTiltMoment t k = tiltMoment t k := by
  unfold regularTiltMoment
  rw [exponentialMoment_zero ht.ne', tiltMoment_eq_mul]
  field_simp

def regularThirdCumulant (t : ℝ) : ℝ :=
  regularTiltMoment t 3 - 3*regularTiltMoment t 1*regularTiltMoment t 2 +
    2*regularTiltMoment t 1^3

theorem regularThirdCumulant_eq {t : ℝ} (ht : 0<t) :
    regularThirdCumulant t = tiltThirdCumulant t := by
  unfold regularThirdCumulant
  rw [regularTiltMoment_eq ht, regularTiltMoment_eq ht, regularTiltMoment_eq ht,
    tiltMoment_one ht]
  exact tiltMoment_three_centered ht

theorem regularThirdCumulant_zero : regularThirdCumulant 0=0 := by
  norm_num [regularThirdCumulant,regularTiltMoment_at_zero]

theorem hasDerivAt_regularThirdCumulant_zero :
    HasDerivAt regularThirdCumulant (-2/15) 0 := by
  have h1 := hasDerivAt_regularTiltMoment_zero 1
  have h2 := hasDerivAt_regularTiltMoment_zero 2
  have h3 := hasDerivAt_regularTiltMoment_zero 3
  have h := (h3.sub ((h1.const_mul 3).mul h2)).add ((h1.pow 3).const_mul 2)
  convert h using 1
  · rfl
  · norm_num [exponentialMoment_at_zero,regularTiltMoment_at_zero]

theorem tendsto_tiltMean_div_zero_right :
    Tendsto (fun t : ℝ=>tiltMean t/t) (𝓝[>] (0:ℝ)) (𝓝 (1/3:ℝ)) := by
  have h0 := hasDerivAt_regularTiltMoment_zero 1
  norm_num [exponentialMoment_at_zero] at h0
  have h := h0.tendsto_slope_zero_right
  norm_num only [zero_add, regularTiltMoment_at_zero, pow_two, neg_one_sq,
    sub_self, zero_div, sub_zero, smul_eq_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [regularTiltMoment_eq ht,tiltMoment_one ht]
  ring

theorem tendsto_tiltThirdCumulant_div_zero_right :
    Tendsto (fun t : ℝ=>tiltThirdCumulant t/t) (𝓝[>] (0:ℝ)) (𝓝 (-2/15:ℝ)) := by
  have h := hasDerivAt_regularThirdCumulant_zero.tendsto_slope_zero_right
  simp only [zero_add,regularThirdCumulant_zero,sub_zero,smul_eq_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [regularThirdCumulant_eq ht]
  ring

/-- Sharp endpoint value of the Langevin scalar bound. -/
theorem tendsto_langevin_ratio_zero_right :
    Tendsto (fun t : ℝ=>-tiltThirdCumulant t/(tiltMean t*tiltVariance t^3))
      (𝓝[>] (0:ℝ)) (𝓝 (54/5:ℝ)) := by
  have h := tendsto_tiltThirdCumulant_div_zero_right.neg.div
    (tendsto_tiltMean_div_zero_right.mul (tendsto_tiltVariance_zero_right.pow 3))
    (by norm_num : (1/3:ℝ)*(1/3)^3≠0)
  norm_num only at h
  have he : (fun t : ℝ=>-(tiltThirdCumulant t/t)/((tiltMean t/t)*tiltVariance t^3)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun t : ℝ=>-tiltThirdCumulant t/(tiltMean t*tiltVariance t^3)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    field_simp [ne_of_gt ht, (tiltMean_pos ht).ne', (tiltVariance_pos ht).ne']
  simpa only [Pi.div_def, Pi.neg_apply] using h.congr' he

end
end ENT.Quantitative
