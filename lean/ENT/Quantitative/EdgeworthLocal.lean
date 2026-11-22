module

public import ENT.Quantitative.EdgeworthCharacteristic
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Local cumulant expansion of the uniform characteristic function from the Taylor expansions of sine and the logarithm. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace ENT.Quantitative
noncomputable section

theorem sin_taylor_five_remainder :
    Tendsto (fun x : ℝ => (Real.sin x - (x-x^3/6+x^5/120))/x^5) (𝓝 0) (𝓝 0) := by
  have hp (x : ℝ) : taylorWithinEval Real.sin 5 univ 0 x = x-x^3/6+x^5/120 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, iteratedDerivWithin_univ,
      show (2:ℕ) = 1+1 from rfl, show (3:ℕ) = 2+1 from rfl,
      show (4:ℕ) = 3+1 from rfl, show (5:ℕ) = 4+1 from rfl]
    ring
  have h := (taylor_isLittleO_univ (f := Real.sin) (n := 5) (x₀ := 0)
    Real.contDiff_sin).tendsto_div_nhds_zero
  simpa only [hp, sub_zero] using h

theorem sinc_taylor_four_limit :
    Tendsto (fun x : ℝ => (Real.sinc x - 1 + x^2/6)/x^4)
      (𝓝[≠] 0) (𝓝 (1/120:ℝ)) := by
  have ht := (sin_taylor_five_remainder.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)).add_const (1/120:ℝ)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  rw [Real.sinc_of_ne_zero hx0]
  field_simp
  ring

theorem sinc_taylor_two_limit :
    Tendsto (fun x : ℝ => (Real.sinc x - 1)/x^2)
      (𝓝[≠] 0) (𝓝 (-1/6:ℝ)) := by
  have hx : Tendsto (fun x : ℝ => x^2) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds).pow 2 :
      Tendsto (fun x : ℝ => x^2) (𝓝[≠] 0) (𝓝 (0^2)))
  have ht := (sinc_taylor_four_limit.mul hx).sub_const (1/6:ℝ)
  norm_num at ht ⊢
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx0
  have hx0 : x ≠ 0 := hx0
  field_simp
  ring

theorem log_one_add_second_remainder :
    Tendsto (fun z : ℝ => (Real.log (1+z)-z+z^2/2)/z^2) (𝓝 0) (𝓝 0) := by
  have hsmall : ∀ᶠ z : ℝ in 𝓝 0, |z| < 1 := by
    have hm : ∀ᶠ z : ℝ in 𝓝 0, z ∈ Metric.ball (0:ℝ) 1 :=
      Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1)
    filter_upwards [hm] with z hz
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hz
  have hbound : ∀ᶠ z : ℝ in 𝓝 0,
      |(Real.log (1+z)-z+z^2/2)/z^2| ≤ |z|/(1-|z|) := by
    filter_upwards [hsmall] with z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    have hb := Real.abs_log_sub_add_sum_range_le (x := -z) (by simpa using hz) 2
    norm_num [Finset.sum_range_succ] at hb
    have he : -z + z^2/2 + Real.log (1+z) = Real.log (1+z)-z+z^2/2 := by ring
    rw [he] at hb
    rw [abs_div, abs_pow, sq_abs]
    apply (div_le_iff₀ (sq_pos_of_ne_zero hz0)).mpr
    convert hb using 1
    rw [show |z|^3 = |z| * z^2 by rw [pow_succ, sq_abs]; ring]
    ring
  have ht : Tendsto (fun z : ℝ => |z|/(1-|z|)) (𝓝 0) (𝓝 (0:ℝ)) := by
    have ha : Tendsto (fun z : ℝ => |z|) (𝓝 0) (𝓝 (0:ℝ)) := by
      simpa using continuous_abs.continuousAt.tendsto (x := (0:ℝ))
    simpa using! ha.div (tendsto_const_nhds.sub ha) (by norm_num : (1:ℝ)-0 ≠ 0)
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr
    (squeeze_zero' (Filter.Eventually.of_forall fun z => abs_nonneg _) hbound ht)

theorem log_sinc_taylor_four_limit :
    Tendsto (fun x : ℝ => (Real.log (Real.sinc x)+x^2/6)/x^4)
      (𝓝[≠] 0) (𝓝 (-1/180:ℝ)) := by
  have hs : Tendsto (fun x : ℝ => Real.sinc x - 1) (𝓝[≠] 0) (𝓝 (0:ℝ)) := by
    simpa using ((Real.continuous_sinc.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)).sub_const 1
  have hr := log_one_add_second_remainder.comp hs
  have ht := sinc_taylor_four_limit.add
    ((hr.sub_const (1/2:ℝ)).mul (sinc_taylor_two_limit.pow 2))
  norm_num at ht ⊢
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx0
  have hx0 : x ≠ 0 := hx0
  by_cases hz : Real.sinc x - 1 = 0
  · have hzx : Real.sinc x = 1 := by linarith
    simp only [hzx, sub_self, Real.log_one, zero_div, zero_pow (by decide : (2:ℕ) ≠ 0),
      mul_zero, add_zero, zero_add]
  · field_simp
    ring

end
end ENT.Quantitative
