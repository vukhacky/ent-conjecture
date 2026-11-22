module

public import ENT.Comparison.EvenJet
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Generic local curvature data for an even potential. Adding a quadratic
term makes its second derivative nonnegative at zero without changing
comparisons between laws of equal variance. -/

@[expose] public section

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace ENT.Comparison

noncomputable section

structure CurvaturePotential (R : ℝ) (V : ℝ → ℝ) : Prop where
  radius_pos : 0 < R
  measurable : Measurable V
  even : Function.Even V
  smooth : ∀ x ∈ Ioo (-R) R, ContDiffAt ℝ 3 V x
  third_nonneg : ∀ x ∈ Ico 0 R, 0 ≤ deriv (deriv (deriv V)) x

namespace CurvaturePotential

def quadraticCorrection (V : ℝ → ℝ) : ℝ := |deriv (deriv V) 0| + 1
def corrected (V : ℝ → ℝ) (x : ℝ) : ℝ := V x + quadraticCorrection V * x ^ 2
def correctedFirst (V : ℝ → ℝ) (x : ℝ) : ℝ := deriv V x + 2 * quadraticCorrection V * x
def correctedSecond (V : ℝ → ℝ) (x : ℝ) : ℝ := deriv (deriv V) x + 2 * quadraticCorrection V

variable {R : ℝ} {V : ℝ → ℝ} (J : CurvaturePotential R V)

include J

theorem correction_pos : 0 < quadraticCorrection V := by
  unfold quadraticCorrection
  linarith [abs_nonneg (deriv (deriv V) 0)]

theorem corrected_measurable : Measurable (corrected V) :=
  J.measurable.add (measurable_const.mul (measurable_id.pow_const 2))

theorem corrected_even : Function.Even (corrected V) := by
  intro x
  unfold corrected
  rw [J.even x]
  ring

theorem corrected_contDiffAt (x : ℝ) (hx : x ∈ Ioo (-R) R) :
    ContDiffAt ℝ 3 (corrected V) x :=
  (J.smooth x hx).add (contDiffAt_const.mul (contDiffAt_id.pow 2))

theorem correctedFirst_contDiffAt (x : ℝ) (hx : x ∈ Ioo (-R) R) :
    ContDiffAt ℝ 2 (correctedFirst V) x :=
  ((J.smooth x hx).derivWithin (by norm_num)).add (contDiffAt_const.mul contDiffAt_id)

theorem correctedSecond_contDiffAt (x : ℝ) (hx : x ∈ Ioo (-R) R) :
    ContDiffAt ℝ 1 (correctedSecond V) x := by
  have h1 : ContDiffAt ℝ 2 (deriv V) x := (J.smooth x hx).derivWithin (by norm_num)
  exact (h1.derivWithin (by norm_num)).add contDiffAt_const

theorem corrected_hasDerivAt (x : ℝ) (hx : x ∈ Ioo (-R) R) :
    HasDerivAt (corrected V) (correctedFirst V x) x := by
  have hv := ((J.smooth x hx).differentiableAt (by norm_num)).hasDerivAt
  convert hv.add (((hasDerivAt_id x).pow 2).const_mul (quadraticCorrection V)) using 1
  · rfl
  · unfold correctedFirst
    simp only [id_eq]
    ring

theorem correctedFirst_hasDerivAt (x : ℝ) (hx : x ∈ Ioo (-R) R) :
    HasDerivAt (correctedFirst V) (correctedSecond V x) x := by
  have h1 : ContDiffAt ℝ 2 (deriv V) x := (J.smooth x hx).derivWithin (by norm_num)
  have hv := (h1.differentiableAt (by norm_num)).hasDerivAt
  convert hv.add ((hasDerivAt_id x).const_mul (2 * quadraticCorrection V)) using 1
  · rfl
  · unfold correctedSecond
    ring

theorem correctedSecond_hasDerivAt (x : ℝ) (hx : x ∈ Ioo (-R) R) :
    HasDerivAt (correctedSecond V) (deriv (deriv (deriv V)) x) x := by
  have h1 : ContDiffAt ℝ 2 (deriv V) x := (J.smooth x hx).derivWithin (by norm_num)
  have h2 : ContDiffAt ℝ 1 (deriv (deriv V)) x := h1.derivWithin (by norm_num)
  exact ((h2.differentiableAt (by norm_num)).hasDerivAt).add_const (2 * quadraticCorrection V)

theorem correctedFirst_odd (x : ℝ) (hx : x ∈ Ioo (-R) R) :
    correctedFirst V (-x) = -correctedFirst V x := by
  have hnx : -x ∈ Ioo (-R) R := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := by
    convert (hasDerivAt_id x).neg using 1
    rfl
  have hc : HasDerivAt (fun y => corrected V (-y)) (-correctedFirst V (-x)) x := by
    convert (J.corrected_hasDerivAt (-x) hnx).comp x hneg using 1
    · rfl
    · ring
  have heq : (fun y => corrected V (-y)) = corrected V := funext J.corrected_even
  rw [heq] at hc
  have hu := hc.unique (J.corrected_hasDerivAt x hx)
  linarith

theorem correctedSecond_even (x : ℝ) (hx : x ∈ Ioo (-R) R) :
    correctedSecond V (-x) = correctedSecond V x := by
  have hnx : -x ∈ Ioo (-R) R := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := by
    convert (hasDerivAt_id x).neg using 1
    rfl
  have hc : HasDerivAt (fun y => correctedFirst V (-y)) (-correctedSecond V (-x)) x := by
    convert (J.correctedFirst_hasDerivAt (-x) hnx).comp x hneg using 1
    · rfl
    · ring
  have heq : (fun y => correctedFirst V (-y)) =ᶠ[𝓝 x] (fun y => -correctedFirst V y) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun y hy => J.correctedFirst_odd y hy)
  have hn : HasDerivAt (fun y => -correctedFirst V y) (-correctedSecond V x) x := by
    convert (J.correctedFirst_hasDerivAt x hx).neg using 1
  have hu := hc.unique (hn.congr_of_eventuallyEq heq)
  linarith

theorem correctedFirst_zero : correctedFirst V 0 = 0 := by
  have h := J.correctedFirst_odd 0 ⟨by linarith [J.radius_pos], J.radius_pos⟩
  simp only [neg_zero] at h
  linarith

theorem correctedSecond_zero_nonneg : 0 ≤ correctedSecond V 0 := by
  unfold correctedSecond quadraticCorrection
  linarith [neg_abs_le (deriv (deriv V) 0), abs_nonneg (deriv (deriv V) 0)]

theorem positive_half_mem_interior (x : ℝ) (hx : x ∈ Ico 0 R) : x ∈ Ioo (-R) R :=
  ⟨by linarith [hx.1, J.radius_pos], hx.2⟩

theorem correctedSecond_monotone : MonotoneOn (correctedSecond V) (Ico 0 R) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 R)
  · intro x hx
    exact (J.correctedSecond_contDiffAt x (J.positive_half_mem_interior x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    exact (J.correctedSecond_hasDerivAt x (J.positive_half_mem_interior x ⟨hx.1.le, hx.2⟩)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    exact J.third_nonneg x ⟨hx.1.le, hx.2⟩

theorem correctedSecond_nonneg (x : ℝ) (hx : x ∈ Ico 0 R) : 0 ≤ correctedSecond V x :=
  le_trans J.correctedSecond_zero_nonneg
    (J.correctedSecond_monotone ⟨le_rfl, J.radius_pos⟩ hx hx.1)

theorem correctedFirst_monotone : MonotoneOn (correctedFirst V) (Ico 0 R) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 R)
  · intro x hx
    exact (J.correctedFirst_contDiffAt x (J.positive_half_mem_interior x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    exact (J.correctedFirst_hasDerivAt x (J.positive_half_mem_interior x ⟨hx.1.le, hx.2⟩)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    exact J.correctedSecond_nonneg x ⟨hx.1.le, hx.2⟩

theorem correctedFirst_nonneg (x : ℝ) (hx : x ∈ Ico 0 R) : 0 ≤ correctedFirst V x := by
  have h := J.correctedFirst_monotone ⟨le_rfl, J.radius_pos⟩ hx hx.1
  simpa only [J.correctedFirst_zero] using h

theorem corrected_monotone : MonotoneOn (corrected V) (Ico 0 R) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 R)
  · intro x hx
    exact (J.corrected_contDiffAt x (J.positive_half_mem_interior x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    exact (J.corrected_hasDerivAt x (J.positive_half_mem_interior x ⟨hx.1.le, hx.2⟩)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    exact J.correctedFirst_nonneg x ⟨hx.1.le, hx.2⟩

theorem corrected_abs (x : ℝ) : corrected V |x| = corrected V x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), J.corrected_even]

theorem corrected_zero_le (x : ℝ) (hx : x ∈ Ioo (-R) R) : corrected V 0 ≤ corrected V x := by
  have h := J.corrected_monotone ⟨le_rfl, J.radius_pos⟩
    ⟨abs_nonneg x, abs_lt.mpr hx⟩ (abs_nonneg x)
  simpa only [J.corrected_abs] using h

theorem contraction_mem (ρ x : ℝ) (hρ : ρ ∈ Icc 0 1) (hx : x ∈ Ioo (-R) R) :
    ρ * x ∈ Ioo (-R) R := by
  apply abs_lt.mp
  rw [abs_mul, abs_of_nonneg hρ.1]
  have hle : ρ * |x| ≤ |x| := by nlinarith [abs_nonneg x, hρ.2]
  exact lt_of_le_of_lt hle (abs_lt.mpr hx)

theorem corrected_contraction_le (ρ x : ℝ) (hρ : ρ ∈ Icc 0 1) (hx : x ∈ Ioo (-R) R) :
    corrected V (ρ * x) ≤ corrected V x := by
  have hxabs := abs_lt.mpr hx
  have hρabs : |ρ * x| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg hρ.1]
    nlinarith [abs_nonneg x, hρ.2]
  have h := J.corrected_monotone ⟨abs_nonneg (ρ * x), lt_of_le_of_lt hρabs hxabs⟩
    ⟨abs_nonneg x, hxabs⟩ hρabs
  simpa only [J.corrected_abs] using h

theorem corrected_contraction_norm_bound (ρ x : ℝ) (hρ : ρ ∈ Icc 0 1)
    (hx : x ∈ Ioo (-R) R) : ‖corrected V (ρ * x)‖ ≤ ‖corrected V x‖ + ‖corrected V 0‖ := by
  have hlo := J.corrected_zero_le (ρ * x) (J.contraction_mem ρ x hρ hx)
  have hhi := J.corrected_contraction_le ρ x hρ hx
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (corrected V 0), abs_nonneg (corrected V x)]
  · linarith [le_abs_self (corrected V x), abs_nonneg (corrected V 0)]

end CurvaturePotential

end
end ENT.Comparison
