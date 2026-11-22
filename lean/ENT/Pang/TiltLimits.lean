module

public import ENT.Pang.Tilt
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Coverage of the positive tilt mean

The mean is a bijection from `(0,∞)` to `(0,1)`. Endpoint limits are proved
by elementary bounds, and existence uses the intermediate value theorem.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace ENT.Pang

noncomputable section

theorem tiltMean_le_sinh_div_cosh_add_one {t : ℝ} (ht : 0 < t) :
    tiltMean t ≤ Real.sinh t / (Real.cosh t + 1) := by
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hc : 0 < Real.cosh t + 1 := by positivity
  have hst : t ≤ Real.sinh t := (Real.self_lt_sinh_iff.mpr ht).le
  have hm := mul_le_mul_of_nonneg_right hst hc.le
  have hi := congrArg (fun z : ℝ => t * z) (Real.cosh_sq_sub_sinh_sq t)
  rw [tiltMean_eq_num ht]
  apply (div_le_div_iff₀ (mul_pos ht hs) hc).mpr
  nlinarith

theorem tendsto_tiltMean_zero_right :
    Tendsto tiltMean (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => Real.sinh t / (Real.cosh t + 1))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => Real.sinh t / (Real.cosh t + 1)) 0 := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num
    change Tendsto (fun t : ℝ => Real.sinh t / (Real.cosh t + 1))
      (𝓝 (0 : ℝ)) (𝓝 (Real.sinh 0 / (Real.cosh 0 + 1))) at hc
    norm_num at hc
    exact hc
  apply squeeze_zero' ?_ ?_ (hu.mono_left nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (tiltMean_pos ht).le
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact tiltMean_le_sinh_div_cosh_add_one ht

theorem one_sub_inv_lt_tiltMean {t : ℝ} (ht : 0 < t) :
    1 - 1 / t < tiltMean t := by
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hcs : Real.sinh t < Real.cosh t := by
    have he : 0 < Real.cosh t - Real.sinh t := by
      rw [Real.cosh_sub_sinh]
      exact Real.exp_pos _
    linarith
  have hc := (one_lt_div hs).mpr hcs
  unfold tiltMean
  linarith

theorem tendsto_tiltMean_atTop : Tendsto tiltMean atTop (𝓝 (1 : ℝ)) := by
  have hi : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hl : Tendsto (fun t : ℝ => 1 - 1 / t) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hi)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (one_sub_inv_lt_tiltMean ht).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (tiltMean_lt_one ht).le

theorem tiltMean_surjOn : SurjOn tiltMean (Ioi (0 : ℝ)) (Ioo (0 : ℝ) 1) := by
  have hc : ContinuousOn tiltMean (Ioi (0 : ℝ)) := by
    intro t ht
    exact (hasDerivAt_tiltMean ht).continuousAt.continuousWithinAt
  exact isPreconnected_Ioi.intermediate_value_Ioo
    (le_principal_iff.mpr self_mem_nhdsWithin)
    (le_principal_iff.mpr (eventually_gt_atTop (0 : ℝ))) hc
    tendsto_tiltMean_zero_right tendsto_tiltMean_atTop

theorem existsUnique_positive_tilt {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) :
    ∃! t : ℝ, 0 < t ∧ tiltMean t = m := by
  obtain ⟨t, ht, htm⟩ := tiltMean_surjOn hm
  refine ⟨t, ⟨ht, htm⟩, ?_⟩
  intro u hu
  exact tiltMean_strictMonoOn.injOn hu.1 ht (hu.2.trans htm.symm)

end
end ENT.Pang
