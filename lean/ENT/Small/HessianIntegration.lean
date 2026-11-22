module

public import ENT.Small.FiveSixAnalysis
public import ENT.Small.EndpointLog
public import ENT.Small.LocalConstants
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Endpoint-safe integration by parts for the local Hessian kernel. -/

@[expose] public section
attribute [local instance 1001] NormedField.toNormedSpace
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace ENT.Small
noncomputable section
open Spline

def logSecondRatio (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x/f x-(deriv f x/f x)^2

def logBoundaryPrimitive (f B : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv B x*Real.log (f x)-B x*(deriv f x/f x)

theorem hasDerivAt_logBoundaryPrimitive (f B : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hB : ContDiff ℝ 2 B) (x : ℝ) (hx : f x≠0) :
    HasDerivAt (logBoundaryPrimitive f B)
      (deriv (deriv B) x*Real.log (f x)-B x*logSecondRatio f x) x := by
  have hdf := (hf.differentiable (by norm_num) x).hasDerivAt
  have hdf2 := (hf.differentiable_deriv_two x).hasDerivAt
  have hdB := (hB.differentiable (by norm_num) x).hasDerivAt
  have hdB2 := (hB.differentiable_deriv_two x).hasDerivAt
  have h := (hdB2.mul (hdf.log hx)).sub (hdB.mul (hdf2.div hdf hx))
  convert h using 1
  · rfl
  · simp only [logSecondRatio, Pi.div_apply, Pi.mul_apply, Pi.sub_apply]
    field_simp
    ring

theorem continuousAt_logSecondRatio (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (x : ℝ) (hx : f x≠0) : ContinuousAt (logSecondRatio f) x := by
  have hdd : Continuous (deriv (deriv f)) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hf.continuous_iteratedDeriv' 2
  exact (hdd.continuousAt.div hf.continuous.continuousAt hx).sub
    (((hf.continuous_deriv (by norm_num)).continuousAt.div hf.continuous.continuousAt hx).pow 2)

theorem continuousAt_logBoundaryPrimitive (f B : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hB : ContDiff ℝ 2 B) (x : ℝ) (hx : f x≠0) :
    ContinuousAt (logBoundaryPrimitive f B) x :=
  (hasDerivAt_logBoundaryPrimitive f B hf hB x hx).continuousAt

theorem continuousOn_from_endpoint_formulas (F L R : ℝ → ℝ) (c : ℝ) (hc : 1<c)
    (hL : Continuous L) (hR : Continuous R)
    (hleft : ∀ x∈Icc (0:ℝ) 1,F x=L x)
    (hright : ∀ x∈Icc (c-1) c,F x=R x)
    (hmid : ∀ x∈Ioo (0:ℝ) c,ContinuousAt F x) : ContinuousOn F (Icc (0:ℝ) c) := by
  intro x hx
  by_cases h0 : x=0
  · subst x
    apply hL.continuousAt.continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with y hy hy1
      exact hleft y ⟨hy.1,hy1.le⟩
    · exact hleft 0 ⟨le_rfl,by norm_num⟩
  · by_cases h1 : x=c
    · subst x
      apply hR.continuousAt.continuousWithinAt.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith : c-1<c))] with y hy hy1
        exact hright y ⟨hy1.le,hy.2⟩
      · exact hright c ⟨by linarith,le_rfl⟩
    · exact (hmid x ⟨lt_of_le_of_ne hx.1 (Ne.symm h0),lt_of_le_of_ne hx.2 h1⟩).continuousWithinAt

theorem weighted_log_integration_by_parts (f B : ℝ → ℝ) {c : ℝ} (hc : 0≤c)
    (hf : ContDiff ℝ 2 f) (hB : ContDiff ℝ 2 B)
    (hpos : ∀ x∈Ioo (0:ℝ) c,0<f x)
    (hlog : IntervalIntegrable (fun x=>Real.log (f x)) volume 0 c)
    (hH : ContinuousOn (fun x=>B x*logSecondRatio f x) (Icc (0:ℝ) c))
    (hG : ContinuousOn (logBoundaryPrimitive f B) (Icc (0:ℝ) c))
    (hG0 : logBoundaryPrimitive f B 0=0) (hGc : logBoundaryPrimitive f B c=0) :
    (∫ x in (0:ℝ)..c,B x*logSecondRatio f x)=
      ∫ x in (0:ℝ)..c,deriv (deriv B) x*Real.log (f x) := by
  have hdd : Continuous (deriv (deriv B)) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hB.continuous_iteratedDeriv' 2
  have hi1 := hlog.continuousOn_mul hdd.continuousOn
  have hi2 : IntervalIntegrable (fun x=>B x*logSecondRatio f x) volume 0 c :=
    hH.intervalIntegrable_of_Icc hc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc hG
    (fun x hx=>hasDerivAt_logBoundaryPrimitive f B hf hB x (hpos x hx).ne') (hi1.sub hi2)
  rw [hG0,hGc,sub_self,intervalIntegral.integral_sub hi1 hi2] at h
  linarith

theorem first_deriv_reflection (f : ℝ → ℝ) (c : ℝ) (hf : ContDiff ℝ 1 f)
    (hsym : ∀ x,f (c-x)=f x) (t : ℝ) : deriv f (c-t)=-deriv f t := by
  have hfun : (fun x=>f (c-x))=f := funext hsym
  have h := ((hf.differentiable (by norm_num) (c-t)).hasDerivAt).comp t
    ((hasDerivAt_const t c).sub (hasDerivAt_id t))
  change HasDerivAt (fun x=>f (c-x)) (deriv f (c-t)*(0-1)) t at h
  rw [hfun] at h
  have hd := h.deriv
  simp only [zero_sub,mul_neg_one] at hd
  linarith

theorem logSecondRatio_reflection (f : ℝ → ℝ) (c : ℝ) (hf : ContDiff ℝ 2 f)
    (hsym : ∀ x,f (c-x)=f x) (t : ℝ) : logSecondRatio f (c-t)=logSecondRatio f t := by
  unfold logSecondRatio
  rw [second_deriv_reflection f c hf hsym t,
    first_deriv_reflection f c (hf.of_le (by norm_num)) hsym t,hsym t]
  ring

theorem logBoundaryPrimitive_reflection (f B : ℝ → ℝ) (c : ℝ)
    (hf : ContDiff ℝ 2 f) (hB : ContDiff ℝ 2 B)
    (hsym : ∀ x,f (c-x)=f x) (hBsym : ∀ x,B (c-x)=B x) (t : ℝ) :
    logBoundaryPrimitive f B (c-t)=-logBoundaryPrimitive f B t := by
  unfold logBoundaryPrimitive
  rw [first_deriv_reflection f c (hf.of_le (by norm_num)) hsym t,
    first_deriv_reflection B c (hB.of_le (by norm_num)) hBsym t,hsym t,hBsym t]
  ring

theorem monomial_jets_on_unit_interval (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℝ) (m : ℕ) (hfm : ∀ x∈Icc (0:ℝ) 1,f x=c*x^m)
    (r : ℕ) (hr : r≤2) (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    iteratedDeriv r f x=c*(m.descFactorial r:ℝ)*x^(m-r) := by
  have h := iteratedDeriv_eq_of_eqOn_Icc r f (fun t=>c*t^m) 0 1 x
    (by norm_num) hx (hf.of_le (by exact_mod_cast hr)).contDiffAt
    (by fun_prop) hfm
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_pow] at h
  simpa only [mul_assoc] using h

theorem unit_density_five_outer_jets (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    unitSumSplineDensity 5 x=x^4/24 ∧ deriv (unitSumSplineDensity 5) x=x^3/6 ∧
      deriv (deriv (unitSumSplineDensity 5)) x=x^2/2 := by
  have h0 (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : unitSumSplineDensity 5 t=(1/24:ℝ)*t^4 := by
    have h := unitSumSplineDensity_eq_cell 5 0 (by decide) (by decide) t ht.1 ht.2
    norm_num [Certificate.splinePiece,Finset.sum_range_succ,Nat.factorial] at h ⊢
    linarith only [h]
  have hf := contDiff_unitSumSplineDensity 2 5 (by decide)
  have h1 := monomial_jets_on_unit_interval _ hf (1/24) 4 h0 1 (by decide) x hx
  have h2 := monomial_jets_on_unit_interval _ hf (1/24) 4 h0 2 (by decide) x hx
  norm_num [iteratedDeriv_succ,iteratedDeriv_zero,Nat.descFactorial_succ] at h1 h2
  exact ⟨by simpa only [div_eq_mul_inv,mul_comm,one_mul] using h0 x hx,by linarith,by linarith⟩

theorem unit_density_six_outer_jets (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    unitSumSplineDensity 6 x=x^5/120 ∧ deriv (unitSumSplineDensity 6) x=x^4/24 ∧
      deriv (deriv (unitSumSplineDensity 6)) x=x^3/6 := by
  have h0 (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : unitSumSplineDensity 6 t=(1/120:ℝ)*t^5 := by
    have h := unitSumSplineDensity_eq_cell 6 0 (by decide) (by decide) t ht.1 ht.2
    norm_num [Certificate.splinePiece,Finset.sum_range_succ,Nat.factorial] at h ⊢
    linarith only [h]
  have hf := contDiff_unitSumSplineDensity 2 6 (by decide)
  have h1 := monomial_jets_on_unit_interval _ hf (1/120) 5 h0 1 (by decide) x hx
  have h2 := monomial_jets_on_unit_interval _ hf (1/120) 5 h0 2 (by decide) x hx
  norm_num [iteratedDeriv_succ,iteratedDeriv_zero,Nat.descFactorial_succ] at h1 h2
  exact ⟨by simpa only [div_eq_mul_inv,mul_comm,one_mul] using h0 x hx,by linarith,by linarith⟩

theorem varianceKernel_five_outer_jets (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    varianceKernel 5 x=x^6/180 ∧ deriv (varianceKernel 5) x=x^5/30 := by
  have h0 (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : varianceKernel 5 t=(1/180:ℝ)*t^6 := by
    simpa [kernelPolynomialFive] using varianceKernel_five_eq_polynomial 0 (by decide) t ht.1 ht.2
  have h1 := monomial_jets_on_unit_interval _ (contDiff_varianceKernel 2 5 (by decide) (by decide))
    (1/180) 6 h0 1 (by decide) x hx
  norm_num [iteratedDeriv_succ,iteratedDeriv_zero,Nat.descFactorial_succ] at h1
  exact ⟨by simpa only [div_eq_mul_inv,mul_comm,one_mul] using h0 x hx,by linarith⟩

theorem varianceKernel_six_outer_jets (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    varianceKernel 6 x=x^7/1260 ∧ deriv (varianceKernel 6) x=x^6/180 := by
  have h0 (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : varianceKernel 6 t=(1/1260:ℝ)*t^7 := by
    simpa [kernelPolynomialSix] using varianceKernel_six_eq_polynomial 0 (by decide) t ht.1 ht.2
  have h1 := monomial_jets_on_unit_interval _ (contDiff_varianceKernel 2 6 (by decide) (by decide))
    (1/1260) 7 h0 1 (by decide) x hx
  norm_num [iteratedDeriv_succ,iteratedDeriv_zero,Nat.descFactorial_succ] at h1
  exact ⟨by simpa only [div_eq_mul_inv,mul_comm,one_mul] using h0 x hx,by linarith⟩

theorem weighted_logSecond_five_outer (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    varianceKernel 5 x*logSecondRatio (unitSumSplineDensity 5) x=-x^4/45 := by
  obtain ⟨hf,hf1,hf2⟩ := unit_density_five_outer_jets x hx
  obtain ⟨hB,hB1⟩ := varianceKernel_five_outer_jets x hx
  rw [logSecondRatio,hf,hf1,hf2,hB]
  by_cases h0 : x=0
  · simp [h0]
  · field_simp
    ring

theorem weighted_logSecond_six_outer (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    varianceKernel 6 x*logSecondRatio (unitSumSplineDensity 6) x=-x^5/252 := by
  obtain ⟨hf,hf1,hf2⟩ := unit_density_six_outer_jets x hx
  obtain ⟨hB,hB1⟩ := varianceKernel_six_outer_jets x hx
  rw [logSecondRatio,hf,hf1,hf2,hB]
  by_cases h0 : x=0
  · simp [h0]
  · field_simp
    ring

theorem logBoundary_five_outer (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    logBoundaryPrimitive (unitSumSplineDensity 5) (varianceKernel 5) x=
      (2/15:ℝ)*x^4*(x*Real.log x)-(Real.log 24/30+1/45)*x^5 := by
  obtain ⟨hf,hf1,hf2⟩ := unit_density_five_outer_jets x hx
  obtain ⟨hB,hB1⟩ := varianceKernel_five_outer_jets x hx
  rw [logBoundaryPrimitive,hf,hf1,hB,hB1]
  by_cases h0 : x=0
  · simp [h0]
  · rw [Real.log_div (pow_ne_zero _ h0) (by norm_num),Real.log_pow]
    field_simp
    ring

theorem logBoundary_six_outer (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    logBoundaryPrimitive (unitSumSplineDensity 6) (varianceKernel 6) x=
      (1/36:ℝ)*x^5*(x*Real.log x)-(Real.log 120/180+1/252)*x^6 := by
  obtain ⟨hf,hf1,hf2⟩ := unit_density_six_outer_jets x hx
  obtain ⟨hB,hB1⟩ := varianceKernel_six_outer_jets x hx
  rw [logBoundaryPrimitive,hf,hf1,hB,hB1]
  by_cases h0 : x=0
  · simp [h0]
  · rw [Real.log_div (pow_ne_zero _ h0) (by norm_num),Real.log_pow]
    field_simp
    ring

def outerWeightedLogSecond (n : ℕ) (x : ℝ) : ℝ :=
  if n=5 then -x^4/45 else -x^5/252

def outerLogBoundary (n : ℕ) (x : ℝ) : ℝ :=
  if n=5 then (2/15:ℝ)*x^4*(x*Real.log x)-(Real.log 24/30+1/45)*x^5
  else (1/36:ℝ)*x^5*(x*Real.log x)-(Real.log 120/180+1/252)*x^6

theorem continuous_outerWeightedLogSecond (n : ℕ) : Continuous (outerWeightedLogSecond n) := by
  unfold outerWeightedLogSecond
  split_ifs <;> fun_prop

theorem continuous_outerLogBoundary (n : ℕ) : Continuous (outerLogBoundary n) := by
  have hlog := Real.continuous_mul_log
  unfold outerLogBoundary
  split_ifs <;> fun_prop

theorem weighted_logSecond_outer (n : ℕ) (hn : n=5 ∨ n=6) (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    varianceKernel n x*logSecondRatio (unitSumSplineDensity n) x=outerWeightedLogSecond n x := by
  rcases hn with rfl | rfl
  · simpa [outerWeightedLogSecond] using weighted_logSecond_five_outer x hx
  · simpa [outerWeightedLogSecond] using weighted_logSecond_six_outer x hx

theorem logBoundary_outer (n : ℕ) (hn : n=5 ∨ n=6) (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    logBoundaryPrimitive (unitSumSplineDensity n) (varianceKernel n) x=outerLogBoundary n x := by
  rcases hn with rfl | rfl
  · simpa [outerLogBoundary] using logBoundary_five_outer x hx
  · simpa [outerLogBoundary] using logBoundary_six_outer x hx

theorem continuousOn_weighted_logSecond_five_six (n : ℕ) (hn : n=5 ∨ n=6) :
    ContinuousOn (fun x=>varianceKernel n x*logSecondRatio (unitSumSplineDensity n) x)
      (Icc (0:ℝ) n) := by
  have hn4 : 4≤n := by omega
  have hfn := contDiff_unitSumSplineDensity 2 n (by omega)
  have hB := contDiff_varianceKernel 2 n (by omega) (by omega)
  have hsym (x : ℝ) :
      varianceKernel n ((n:ℝ)-x)*logSecondRatio (unitSumSplineDensity n) ((n:ℝ)-x)=
        varianceKernel n x*logSecondRatio (unitSumSplineDensity n) x := by
    rw [varianceKernel_reflection n (by omega),
      logSecondRatio_reflection _ n hfn (unitSumSplineDensity_reflection n (by omega))]
  apply continuousOn_from_endpoint_formulas _ (outerWeightedLogSecond n)
    (fun x=>outerWeightedLogSecond n ((n:ℝ)-x)) n (by exact_mod_cast (by omega : 1<n))
    (continuous_outerWeightedLogSecond n)
    ((continuous_outerWeightedLogSecond n).comp (continuous_const.sub continuous_id))
    (weighted_logSecond_outer n hn)
  · intro x hx
    rw [←hsym x]
    exact weighted_logSecond_outer n hn _ ⟨by linarith [hx.2],by linarith [hx.1]⟩
  · intro x hx
    exact hB.continuous.continuousAt.mul (continuousAt_logSecondRatio _ hfn x
      (unitSumSplineDensity_pos n (by omega) x hx.1 hx.2).ne')

theorem continuousOn_logBoundary_five_six (n : ℕ) (hn : n=5 ∨ n=6) :
    ContinuousOn (logBoundaryPrimitive (unitSumSplineDensity n) (varianceKernel n)) (Icc (0:ℝ) n) := by
  have hn4 : 4≤n := by omega
  have hfn := contDiff_unitSumSplineDensity 2 n (by omega)
  have hB := contDiff_varianceKernel 2 n (by omega) (by omega)
  have hsym := logBoundaryPrimitive_reflection _ _ n hfn hB
    (unitSumSplineDensity_reflection n (by omega)) (varianceKernel_reflection n (by omega))
  apply continuousOn_from_endpoint_formulas _ (outerLogBoundary n)
    (fun x=>-outerLogBoundary n ((n:ℝ)-x)) n (by exact_mod_cast (by omega : 1<n))
    (continuous_outerLogBoundary n)
    (((continuous_outerLogBoundary n).comp (continuous_const.sub continuous_id)).neg)
    (logBoundary_outer n hn)
  · intro x hx
    have h := logBoundary_outer n hn ((n:ℝ)-x) ⟨by linarith [hx.2],by linarith [hx.1]⟩
    have hs := hsym x
    linarith
  · intro x hx
    exact continuousAt_logBoundaryPrimitive _ _ hfn hB x
      (unitSumSplineDensity_pos n (by omega) x hx.1 hx.2).ne'

theorem logBoundary_five_six_endpoints (n : ℕ) (hn : n=5 ∨ n=6) :
    logBoundaryPrimitive (unitSumSplineDensity n) (varianceKernel n) 0=0 ∧
      logBoundaryPrimitive (unitSumSplineDensity n) (varianceKernel n) n=0 := by
  have h0 := logBoundary_outer n hn 0 ⟨le_rfl,by norm_num⟩
  have h00 : outerLogBoundary n 0=0 := by simp [outerLogBoundary]
  have hfn := contDiff_unitSumSplineDensity 2 n (by omega)
  have hB := contDiff_varianceKernel 2 n (by omega) (by omega)
  have hs := logBoundaryPrimitive_reflection _ _ n hfn hB
    (unitSumSplineDensity_reflection n (by omega)) (varianceKernel_reflection n (by omega)) 0
  rw [h00] at h0
  simpa only [sub_zero,h0,neg_zero] using And.intro h0 hs

theorem hessian_kernel_integral_five_six (n : ℕ) (hn : n=5 ∨ n=6) :
    ((n:ℝ)/4)*(∫ t in (0:ℝ)..n,varianceKernel n t*logSecondRatio (unitSumSplineDensity n) t)=
      smallKappa n-1 := by
  have hfn := contDiff_unitSumSplineDensity 2 n (by omega)
  have hB := contDiff_varianceKernel 2 n (by omega) (by omega)
  have hends := logBoundary_five_six_endpoints n hn
  have hi := weighted_log_integration_by_parts _ _ (Nat.cast_nonneg n) hfn hB
    (fun x hx=>unitSumSplineDensity_pos n (by omega) x hx.1 hx.2) (intervalIntegrable_log_unitSumSplineDensity n (by omega))
    (continuousOn_weighted_logSecond_five_six n hn) (continuousOn_logBoundary_five_six n hn)
    hends.1 hends.2
  have hsecond (t : ℝ) (ht : t∈Icc (0:ℝ) n) :
      deriv (deriv (varianceKernel n)) t=4*(unitSumSplineDensity n t-unitSumSplineDensity (n-2) (t-1)) := by
    rcases hn with rfl | rfl
    · exact varianceKernel_five_second t ht
    · exact varianceKernel_six_second t ht
  have heq : (∫ t in (0:ℝ)..n,deriv (deriv (varianceKernel n)) t*Real.log (unitSumSplineDensity n t))=
      -4*(∫ t in (0:ℝ)..n,(unitSumSplineDensity (n-2) (t-1)-unitSumSplineDensity n t)*
        Real.log (unitSumSplineDensity n t)) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le (Nat.cast_nonneg n)] at ht
    rw [hsecond t ht]
    ring
  rw [hi,heq]
  unfold smallKappa
  ring

theorem second_deriv_log_eq_ratio (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (x : ℝ) (hx : f x≠0) :
    deriv (deriv (fun t=>Real.log (f t))) x=logSecondRatio f x := by
  have hne : ∀ᶠ y in 𝓝 x,f y≠0 := hf.continuous.continuousAt.eventually_ne hx
  have heq : deriv (fun t=>Real.log (f t))=ᶠ[𝓝 x](fun y=>deriv f y/f y) := by
    filter_upwards [hne] with y hy
    exact (((hf.differentiable (by norm_num) y).hasDerivAt).log hy).deriv
  rw [heq.deriv_eq]
  have h := ((hf.differentiable_deriv_two x).hasDerivAt).div
    ((hf.differentiable (by norm_num) x).hasDerivAt) hx
  have hd := h.deriv
  change deriv (fun y=>deriv f y/f y) x=_ at hd
  rw [hd]
  unfold logSecondRatio
  field_simp

end
end ENT.Small
