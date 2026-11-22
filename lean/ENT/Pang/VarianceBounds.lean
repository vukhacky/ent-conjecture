module

public import ENT.Pang.Moments
public import ENT.Pang.SkewSign
public import ENT.Pang.TiltLimits
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The uniform upper variance bound for positive tilts

The zero-tilt limit is obtained from genuine interval moments by dominated
convergence. Combined with strict decrease, it gives `0 < v(t) < 1/3`.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology Interval

namespace ENT.Pang

noncomputable section

theorem continuousAt_exponentialMoment_zero (k : ℕ) :
    ContinuousAt (fun t : ℝ => exponentialMoment t k) 0 := by
  unfold exponentialMoment
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ : ℝ => Real.exp 1)
  · exact Eventually.of_forall (fun t =>
      (show Continuous (fun x : ℝ => x ^ k * Real.exp (t * x)) by
        fun_prop).aestronglyMeasurable)
  · filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with t ht
    apply Eventually.of_forall
    intro x hx
    have hx' : x ∈ Ioc (-1 : ℝ) 1 := by
      simpa only [uIoc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] using hx
    have hxt : |x| ≤ 1 := abs_le.mpr ⟨hx'.1.le, hx'.2⟩
    have htt : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
    have htx : t * x ≤ 1 := by
      calc
        t * x ≤ |t * x| := le_abs_self _
        _ = |t| * |x| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul htt hxt (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hpow : ‖x ^ k‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg x) (by simpa only [Real.norm_eq_abs] using hxt)
    calc
      ‖x ^ k * Real.exp (t * x)‖ = ‖x ^ k‖ * Real.exp (t * x) := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ 1 * Real.exp 1 :=
        mul_le_mul hpow (Real.exp_le_exp.mpr htx) (Real.exp_pos _).le (by norm_num)
      _ = Real.exp 1 := one_mul _
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun x _ => by fun_prop)

theorem integral_pow_unit (k : ℕ) :
    (∫ x in (-1 : ℝ)..1, x ^ k) =
      (1 - (-1 : ℝ) ^ (k + 1)) / (k + 1 : ℝ) := by
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  have hd : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => y ^ (k + 1) / (k + 1 : ℝ)) (x ^ k) x := by
    intro x
    have h := ((hasDerivAt_id x).pow (k + 1)).div_const (k + 1 : ℝ)
    apply h.congr_deriv
    simp only [id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  have hi : IntervalIntegrable (fun x : ℝ => x ^ k) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi
  simpa only [one_pow, sub_div] using h

theorem exponentialMoment_at_zero (k : ℕ) :
    exponentialMoment 0 k = (1 - (-1 : ℝ) ^ (k + 1)) / (k + 1 : ℝ) := by
  unfold exponentialMoment
  simp only [zero_mul, Real.exp_zero, mul_one]
  exact integral_pow_unit k

theorem tendsto_tiltNormalizer_zero_right :
    Tendsto (fun t : ℝ => t / (2 * Real.sinh t)) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by
  have h : Tendsto (fun t : ℝ => (1 / 2 : ℝ) / (Real.sinh t / t))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2 : ℝ) / 1)) :=
    tendsto_const_nhds.div tendsto_sinh_div_zero_right (by norm_num)
  have heq : (fun t : ℝ => (1 / 2 : ℝ) / (Real.sinh t / t)) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => t / (2 * Real.sinh t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
    field_simp [ht.ne', hs]
  simpa only [div_one] using h.congr' heq

theorem tendsto_tiltMoment_two_zero_right :
    Tendsto (fun t : ℝ => tiltMoment t 2) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 3)) := by
  have hm : Tendsto (fun t : ℝ => exponentialMoment t 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / 3)) := by
    have h : Tendsto (fun t : ℝ => exponentialMoment t 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (exponentialMoment 0 2)) :=
      (continuousAt_exponentialMoment_zero 2).mono_left nhdsWithin_le_nhds
    norm_num [exponentialMoment_at_zero] at h
    exact h
  have h := tendsto_tiltNormalizer_zero_right.mul hm
  norm_num only at h
  have heq : (fun t : ℝ => t / (2 * Real.sinh t) * exponentialMoment t 2) =
      (fun t : ℝ => tiltMoment t 2) := by
    funext t
    exact (tiltMoment_eq_mul t 2).symm
  rw [heq] at h
  exact h

theorem tendsto_tiltVariance_zero_right :
    Tendsto tiltVariance (𝓝[>] (0 : ℝ)) (𝓝 (1 / 3)) := by
  have h := tendsto_tiltMoment_two_zero_right.sub (tendsto_tiltMean_zero_right.pow 2)
  norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact tiltMoment_two_sub_mean_sq ht

theorem tiltVariance_lt_one_third {t : ℝ} (ht : 0 < t) :
    tiltVariance t < 1 / 3 := by
  have ht2 : 0 < t / 2 := by linarith
  have hb : tiltVariance (t / 2) ≤ 1 / 3 := by
    apply ge_of_tendsto tendsto_tiltVariance_zero_right
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ht2).filter_mono nhdsWithin_le_nhds] with x hx hxt
    exact (tiltVariance_strictAntiOn hx ht2 hxt).le
  exact lt_of_lt_of_le (tiltVariance_strictAntiOn ht2 ht (by linarith)) hb

theorem tiltVariance_mem_Ioo {t : ℝ} (ht : 0 < t) :
    tiltVariance t ∈ Ioo (0 : ℝ) (1 / 3) :=
  ⟨tiltVariance_pos ht, tiltVariance_lt_one_third ht⟩

end
end ENT.Pang
