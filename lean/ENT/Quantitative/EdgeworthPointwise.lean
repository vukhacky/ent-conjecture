module

public import ENT.Quantitative.EdgeworthLocal

/-! The first pointwise Fourier Edgeworth correction for the genuine
standardized continuous uniform sum. The normalization and the coefficient
`-u^4/20` are derived, not postulated. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace ENT.Quantitative
noncomputable section

def uniformFourierFactor (n : ℕ) (u : ℝ) : ℝ := Real.sinc (uniformSumFrequency n u)^n

theorem uniformSumFrequency_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => uniformSumFrequency n u) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs := (Real.continuous_sqrt.tendsto (0:ℝ)).comp hi
  change Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)⁻¹)) atTop (𝓝 (Real.sqrt 0)) at hs
  simp only [Real.sqrt_inv, Real.sqrt_zero, Function.comp_apply] at hs
  simpa only [uniformSumFrequency, mul_zero, zero_mul] using
    (hs.const_mul (Real.sqrt 3)).mul_const u

theorem uniformSumFrequency_tendsto_nhdsNE {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun n : ℕ => uniformSumFrequency n u) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (uniformSumFrequency_tendsto u) ?_
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  change uniformSumFrequency n u ≠ 0
  unfold uniformSumFrequency
  exact mul_ne_zero (mul_ne_zero (by positivity) (inv_ne_zero (by positivity))) hu

def uniformLogCorrection (n : ℕ) (u : ℝ) : ℝ :=
  (n:ℝ) * Real.log (Real.sinc (uniformSumFrequency n u)) + u^2/2

theorem uniformLogCorrection_scaled_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)*uniformLogCorrection n u)
      atTop (𝓝 (-u^4/20)) := by
  by_cases hu : u = 0
  · subst u
    simpa [uniformLogCorrection, uniformSumFrequency] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  have ht := (log_sinc_taylor_four_limit.comp (uniformSumFrequency_tendsto_nhdsNE hu)).mul_const
    (9*u^4)
  have he : (fun n : ℕ =>
      (Real.log (Real.sinc (uniformSumFrequency n u)) + (uniformSumFrequency n u)^2/6) /
        (uniformSumFrequency n u)^4 * (9*u^4)) =ᶠ[atTop]
        (fun n : ℕ => (n:ℝ)*uniformLogCorrection n u) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : 0 < n := by omega
    have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn0)
    rw [show (uniformSumFrequency n u)^4 = ((uniformSumFrequency n u)^2)^2 by ring,
      uniformSumFrequency_sq hn0]
    unfold uniformLogCorrection
    field_simp
    ring
  convert ht.congr' he using 1 <;> ring

theorem uniformLogCorrection_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => uniformLogCorrection n u) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := (uniformLogCorrection_scaled_tendsto u).mul hi
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

theorem uniformFourierFactor_eventually_eq_exp (u : ℝ) :
    (fun n : ℕ => uniformFourierFactor n u) =ᶠ[atTop]
      (fun n : ℕ => Pang.gaussianWeight u * Real.exp (uniformLogCorrection n u)) := by
  have hs := Real.continuous_sinc.tendsto (0:ℝ) |>.comp (uniformSumFrequency_tendsto u)
  simp only [Real.sinc_zero] at hs
  have hpos := (tendsto_order.mp hs).1 0 (by norm_num)
  filter_upwards [hpos] with n hn
  change 0 < Real.sinc (uniformSumFrequency n u) at hn
  unfold uniformFourierFactor Pang.gaussianWeight uniformLogCorrection
  rw [← Real.exp_add]
  rw [show -u^2/2 + ((n:ℝ)*Real.log (Real.sinc (uniformSumFrequency n u)) + u^2/2) =
    (n:ℝ)*Real.log (Real.sinc (uniformSumFrequency n u)) by ring,
    Real.exp_natCast_mul, Real.exp_log hn]

theorem scaled_exp_sub_one_tendsto {r : ℕ → ℝ} {c : ℝ}
    (hr : Tendsto (fun n : ℕ => (n:ℝ)*r n) atTop (𝓝 c))
    (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n:ℝ)*(Real.exp (r n)-1)) atTop (𝓝 c) := by
  have hc : ContinuousAt (dslope Real.exp 0) 0 :=
    continuousAt_dslope_same.mpr Real.differentiable_exp.differentiableAt
  have hs := hc.tendsto.comp hr0
  simp only [dslope_same, Real.deriv_exp, Real.exp_zero] at hs
  have ht := hr.mul hs
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [] with n
  have he := sub_smul_dslope Real.exp 0 (r n)
  simp only [sub_zero, smul_eq_mul, Real.exp_zero] at he
  change (n:ℝ)*r n*dslope Real.exp 0 (r n) = _
  rw [mul_assoc, he]

theorem uniformFourierFactor_first_correction (u : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)*(uniformFourierFactor n u-Pang.gaussianWeight u))
      atTop (𝓝 (-u^4/20*Pang.gaussianWeight u)) := by
  have ht := (scaled_exp_sub_one_tendsto (uniformLogCorrection_scaled_tendsto u)
    (uniformLogCorrection_tendsto u)).mul_const (Pang.gaussianWeight u)
  apply ht.congr'
  filter_upwards [uniformFourierFactor_eventually_eq_exp u] with n hn
  rw [hn]
  ring

theorem uniformFourierFactor_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => uniformFourierFactor n u) atTop (𝓝 (Pang.gaussianWeight u)) := by
  have ht : Tendsto (fun n : ℕ => Pang.gaussianWeight u * Real.exp (uniformLogCorrection n u))
      atTop (𝓝 (Pang.gaussianWeight u)) := by
    simpa only [Real.exp_zero, mul_one] using
      ((uniformLogCorrection_tendsto u).rexp).const_mul (Pang.gaussianWeight u)
  exact ht.congr' (uniformFourierFactor_eventually_eq_exp u).symm

theorem charFun_standardizedDiagonal_first_correction (u : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ) •
      (charFun (standardizedProjectionLaw (diagonal n)) u - (Pang.gaussianWeight u : ℂ)))
      atTop (𝓝 ((-u^4/20*Pang.gaussianWeight u : ℝ) : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (uniformFourierFactor_first_correction u)
  change Tendsto (fun n : ℕ => (((n:ℝ)*(uniformFourierFactor n u-Pang.gaussianWeight u) : ℝ) : ℂ))
    atTop (𝓝 ((-u^4/20*Pang.gaussianWeight u : ℝ) : ℂ)) at h
  simpa only [Function.comp_apply, charFun_standardizedDiagonal, uniformFourierFactor,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow, Complex.real_smul] using h

end
end ENT.Quantitative
