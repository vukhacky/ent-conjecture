module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Derivatives of the log-partition function of the positive exponential tilt on `t > 0`, as in Section 3 of Pang. -/

@[expose] public section

set_option autoImplicit false

open Set

namespace ENT.Pang

noncomputable section

/-- Explicit log partition on the positive-tilt domain. All analytic theorems
below carry `0 < t`; no claim about this formula's derivatives at zero is made. -/
def logPartition (t : ℝ) : ℝ := Real.log (Real.sinh t / t)

/-- The explicit first derivative of the positive-tilt log partition. -/
def tiltMean (t : ℝ) : ℝ := Real.cosh t / Real.sinh t - 1 / t

/-- The explicit second derivative. Its probability interpretation is proved
in a separate density module. -/
def tiltVariance (t : ℝ) : ℝ := 1 / t ^ 2 - 1 / Real.sinh t ^ 2

/-- The explicit third derivative of the positive-tilt log partition. -/
def tiltThirdCumulant (t : ℝ) : ℝ :=
  2 * Real.cosh t / Real.sinh t ^ 3 - 2 / t ^ 3

theorem tiltMean_eq_num {t : ℝ} (ht : 0 < t) :
    tiltMean t = (t * Real.cosh t - Real.sinh t) / (t * Real.sinh t) := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  unfold tiltMean
  field_simp [ht.ne', hs]

theorem tiltVariance_eq_num {t : ℝ} (ht : 0 < t) :
    tiltVariance t =
      (Real.sinh t ^ 2 - t ^ 2) / (t ^ 2 * Real.sinh t ^ 2) := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  unfold tiltVariance
  field_simp [ht.ne', hs]

theorem logPartition_pos {t : ℝ} (ht : 0 < t) : 0 < logPartition t := by
  unfold logPartition
  apply Real.log_pos
  exact (one_lt_div ht).mpr (Real.self_lt_sinh_iff.mpr ht)

theorem hasDerivAt_logPartition {t : ℝ} (ht : 0 < t) :
    HasDerivAt logPartition (tiltMean t) t := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have h := ((Real.hasDerivAt_sinh t).div (hasDerivAt_id t) ht.ne').log
    (div_ne_zero hs ht.ne')
  apply h.congr_deriv
  change (Real.cosh t * t - Real.sinh t * 1) / t ^ 2 / (Real.sinh t / t) =
    Real.cosh t / Real.sinh t - 1 / t
  field_simp [ht.ne', hs]
  <;> ring

theorem hasDerivAt_tiltMean {t : ℝ} (ht : 0 < t) :
    HasDerivAt tiltMean (tiltVariance t) t := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have hnum : Real.sinh t * Real.sinh t - Real.cosh t * Real.cosh t = -1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have h := ((Real.hasDerivAt_cosh t).div (Real.hasDerivAt_sinh t) hs).sub
    ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht.ne')
  apply h.congr_deriv
  change (Real.sinh t * Real.sinh t - Real.cosh t * Real.cosh t) / Real.sinh t ^ 2 -
    (0 * t - 1 * 1) / t ^ 2 = 1 / t ^ 2 - 1 / Real.sinh t ^ 2
  rw [hnum]
  ring

theorem hasDerivAt_tiltVariance {t : ℝ} (ht : 0 < t) :
    HasDerivAt tiltVariance (tiltThirdCumulant t) t := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have h := ((hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 2)
      (pow_ne_zero 2 ht.ne')).sub
    ((hasDerivAt_const t (1 : ℝ)).div ((Real.hasDerivAt_sinh t).pow 2)
      (pow_ne_zero 2 hs))
  apply h.congr_deriv
  change (0 * t ^ 2 - 1 * (2 * t ^ (2 - 1) * 1)) / (t ^ 2) ^ 2 -
    (0 * Real.sinh t ^ 2 - 1 * (2 * Real.sinh t ^ (2 - 1) * Real.cosh t)) /
      (Real.sinh t ^ 2) ^ 2 = 2 * Real.cosh t / Real.sinh t ^ 3 - 2 / t ^ 3
  field_simp [ht.ne', hs]
  <;> ring

theorem deriv_logPartition {t : ℝ} (ht : 0 < t) :
    deriv logPartition t = tiltMean t :=
  (hasDerivAt_logPartition ht).deriv

theorem deriv_tiltMean {t : ℝ} (ht : 0 < t) :
    deriv tiltMean t = tiltVariance t :=
  (hasDerivAt_tiltMean ht).deriv

theorem deriv_tiltVariance {t : ℝ} (ht : 0 < t) :
    deriv tiltVariance t = tiltThirdCumulant t :=
  (hasDerivAt_tiltVariance ht).deriv

theorem tiltVariance_pos {t : ℝ} (ht : 0 < t) : 0 < tiltVariance t := by
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hst : t < Real.sinh t := Real.self_lt_sinh_iff.mpr ht
  rw [tiltVariance_eq_num ht]
  apply div_pos
  · nlinarith
  · positivity

theorem tiltMean_strictMonoOn : StrictMonoOn tiltMean (Ioi (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi _) ?_ ?_
  · intro t ht
    exact (hasDerivAt_tiltMean ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    rw [deriv_tiltMean ht']
    exact tiltVariance_pos ht'

theorem mean_numerator_pos {t : ℝ} (ht : 0 < t) :
    0 < t * Real.cosh t - Real.sinh t := by
  have hd : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => y * Real.cosh y - Real.sinh y)
        (x * Real.sinh x) x := by
    intro x
    have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x)
    apply h.congr_deriv
    change 1 * Real.cosh x + x * Real.sinh x - Real.cosh x = x * Real.sinh x
    ring
  have hm : StrictMonoOn (fun x : ℝ => x * Real.cosh x - Real.sinh x)
      (Ici (0 : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · fun_prop
    · intro x hx
      rw [interior_Ici, mem_Ioi] at hx
      rw [(hd x).deriv]
      exact mul_pos hx (Real.sinh_pos_iff.mpr hx)
  simpa using hm (show (0 : ℝ) ∈ Ici 0 by simp) (le_of_lt ht) ht

theorem tiltMean_pos {t : ℝ} (ht : 0 < t) : 0 < tiltMean t := by
  rw [tiltMean_eq_num ht]
  exact div_pos (mean_numerator_pos ht) (mul_pos ht (Real.sinh_pos_iff.mpr ht))

theorem tiltMean_lt_one {t : ℝ} (ht : 0 < t) : tiltMean t < 1 := by
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have he : (2 * t + 1) * Real.exp (-t) < Real.exp t := by
    have h := mul_lt_mul_of_pos_right
      (Real.add_one_lt_exp (show 2 * t ≠ 0 by linarith)) (Real.exp_pos (-t))
    have heq : Real.exp (2 * t) * Real.exp (-t) = Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [heq] at h
  have hc : t * (Real.cosh t - Real.sinh t) = t * Real.exp (-t) := by
    rw [Real.cosh_sub_sinh]
  have hss : 2 * Real.sinh t = Real.exp t - Real.exp (-t) := by
    rw [Real.sinh_eq]
    ring
  rw [tiltMean_eq_num ht]
  apply (div_lt_one (mul_pos ht hs)).mpr
  nlinarith

theorem tiltMean_mem_Ioo {t : ℝ} (ht : 0 < t) : tiltMean t ∈ Ioo (0 : ℝ) 1 :=
  ⟨tiltMean_pos ht, tiltMean_lt_one ht⟩

end
end ENT.Pang
