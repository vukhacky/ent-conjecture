module

public import ENT.Pang.Tilt
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Strict negativity of the third tilt cumulant

An elementary hyperbolic-function proof. This supplies only the sign portion
of Pang's Lemma 4.1; it does not assert the standardized bound by two or the
fifth/third moment ratio bound.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace ENT.Pang

noncomputable section

def skewAux (t : ℝ) : ℝ :=
  t * (3 + 2 * Real.sinh t ^ 2) - 3 * Real.sinh t * Real.cosh t

theorem hasDerivAt_skewAux (t : ℝ) :
    HasDerivAt skewAux
      (4 * Real.sinh t * (t * Real.cosh t - Real.sinh t)) t := by
  have h := ((hasDerivAt_id t).mul
      ((hasDerivAt_const t (3 : ℝ)).add (((Real.hasDerivAt_sinh t).pow 2).const_mul 2))).sub
    (((Real.hasDerivAt_sinh t).mul (Real.hasDerivAt_cosh t)).const_mul 3)
  change HasDerivAt (fun x : ℝ => x * (3 + 2 * Real.sinh x ^ 2) -
    3 * (Real.sinh x * Real.cosh x))
    (1 * (3 + 2 * Real.sinh t ^ 2) +
      t * (0 + 2 * (2 * Real.sinh t ^ (2 - 1) * Real.cosh t)) -
      3 * (Real.cosh t * Real.cosh t + Real.sinh t * Real.sinh t)) t at h
  have hf : (fun x : ℝ => x * (3 + 2 * Real.sinh x ^ 2) -
      3 * (Real.sinh x * Real.cosh x)) = skewAux := by
    funext x
    unfold skewAux
    ring
  rw [hf] at h
  apply h.congr_deriv
  simp only [Nat.reduceSub, pow_one]
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

theorem skewAux_pos {t : ℝ} (ht : 0 < t) : 0 < skewAux t := by
  have hm : StrictMonoOn skewAux (Ici (0 : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · unfold skewAux
      fun_prop
    · intro x hx
      rw [interior_Ici, mem_Ioi] at hx
      rw [(hasDerivAt_skewAux x).deriv]
      exact mul_pos (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr hx))
        (mean_numerator_pos hx)
  simpa [skewAux] using hm (show (0 : ℝ) ∈ Ici 0 by simp) (le_of_lt ht) ht

def skewLogRatio (t : ℝ) : ℝ :=
  3 * logPartition t - Real.log (Real.cosh t)

theorem hasDerivAt_skewLogRatio {t : ℝ} (ht : 0 < t) :
    HasDerivAt skewLogRatio
      (3 * tiltMean t - Real.sinh t / Real.cosh t) t := by
  have h := ((hasDerivAt_logPartition ht).const_mul 3).sub
    ((Real.hasDerivAt_cosh t).log (Real.cosh_pos t).ne')
  unfold skewLogRatio
  exact h

theorem skewLogRatio_derivative_eq {t : ℝ} (ht : 0 < t) :
    3 * tiltMean t - Real.sinh t / Real.cosh t =
      skewAux t / (t * Real.sinh t * Real.cosh t) := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have hc : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  have hi := congrArg (fun x : ℝ => t * x) (Real.cosh_sq_sub_sinh_sq t)
  unfold tiltMean skewAux
  field_simp [ht.ne', hs, hc]
  nlinarith

theorem skewLogRatio_strictMonoOn : StrictMonoOn skewLogRatio (Ioi (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi _) ?_ ?_
  · intro t ht
    exact (hasDerivAt_skewLogRatio ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    rw [(hasDerivAt_skewLogRatio ht').deriv, skewLogRatio_derivative_eq ht']
    exact div_pos (skewAux_pos ht')
      (mul_pos (mul_pos ht' (Real.sinh_pos_iff.mpr ht')) (Real.cosh_pos t))

theorem tendsto_sinh_div_zero_right :
    Tendsto (fun t : ℝ => Real.sinh t / t) (𝓝[>] 0) (𝓝 1) := by
  simpa only [zero_add, Real.sinh_zero, sub_zero, smul_eq_mul, Real.cosh_zero,
    div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_sinh (0 : ℝ)).tendsto_slope_zero_right

theorem tendsto_logPartition_zero_right :
    Tendsto logPartition (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  unfold logPartition
  have h := tendsto_sinh_div_zero_right.log (show (1 : ℝ) ≠ 0 by norm_num)
  simpa only [Real.log_one] using h

theorem tendsto_skewLogRatio_zero_right :
    Tendsto skewLogRatio (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcosh : Tendsto Real.cosh (𝓝[>] (0 : ℝ)) (𝓝 (Real.cosh 0)) :=
    (Real.continuous_cosh.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc := hcosh.log (by simp : Real.cosh (0 : ℝ) ≠ 0)
  have h := (tendsto_logPartition_zero_right.const_mul 3).sub hc
  unfold skewLogRatio
  simpa only [Real.cosh_zero, Real.log_one, mul_zero, sub_zero] using h

theorem skewLogRatio_pos {t : ℝ} (ht : 0 < t) : 0 < skewLogRatio t := by
  have ht2 : 0 < t / 2 := by linarith
  have hnonneg : 0 ≤ skewLogRatio (t / 2) := by
    apply le_of_tendsto tendsto_skewLogRatio_zero_right
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ht2).filter_mono nhdsWithin_le_nhds] with x hx hxt
    exact (skewLogRatio_strictMonoOn hx ht2 hxt).le
  exact lt_of_le_of_lt hnonneg
    (skewLogRatio_strictMonoOn ht2 ht (by linarith))

theorem sinh_cube_gt_t_cube_cosh {t : ℝ} (ht : 0 < t) :
    t ^ 3 * Real.cosh t < Real.sinh t ^ 3 := by
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hc : 0 < Real.cosh t := Real.cosh_pos t
  have hratio : 0 < (Real.sinh t / t) ^ 3 / Real.cosh t := by positivity
  have hlog : Real.log ((Real.sinh t / t) ^ 3 / Real.cosh t) = skewLogRatio t := by
    rw [Real.log_div (pow_ne_zero 3 (div_ne_zero hs.ne' ht.ne')) hc.ne', Real.log_pow]
    rfl
  have hgt : 1 < (Real.sinh t / t) ^ 3 / Real.cosh t := by
    apply (Real.log_pos_iff hratio.le).mp
    rw [hlog]
    exact skewLogRatio_pos ht
  have hgt' := (lt_div_iff₀ hc).mp hgt
  rw [div_pow] at hgt'
  have hfinal := (lt_div_iff₀ (pow_pos ht 3)).mp hgt'
  nlinarith

theorem tiltThirdCumulant_neg {t : ℝ} (ht : 0 < t) : tiltThirdCumulant t < 0 := by
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hgap := sinh_cube_gt_t_cube_cosh ht
  unfold tiltThirdCumulant
  apply sub_neg.mpr
  apply (div_lt_div_iff₀ (pow_pos hs 3) (pow_pos ht 3)).mpr
  nlinarith

theorem tiltVariance_strictAntiOn : StrictAntiOn tiltVariance (Ioi (0 : ℝ)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi _) ?_ ?_
  · intro t ht
    exact (hasDerivAt_tiltVariance ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    rw [deriv_tiltVariance ht']
    exact tiltThirdCumulant_neg ht'

end
end ENT.Pang
