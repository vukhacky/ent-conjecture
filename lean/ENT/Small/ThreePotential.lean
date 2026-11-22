module

public import ENT.Small.ThreeDensity
public import ENT.Small.EnclosuresThree
public import ENT.Spline.PositiveInterior
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The actual dimension-three potential is C¹ across its interior knot, and its
piecewise second derivative is bounded by six on the local interval. -/

@[expose] public section

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace ENT.Small

noncomputable section

def threeCenterPotential (x : ℝ) : ℝ :=
  -Real.log ((3 * Real.sqrt (3 : ℝ) / 8) * (1 - x ^ 2))

def threeOuterPotential (x : ℝ) : ℝ :=
  -Real.log ((3 * Real.sqrt (3 : ℝ) / 16) * (Real.sqrt (3 : ℝ) - x) ^ 2)

theorem three_potential_eq_center {x : ℝ} (hx : x ∈ Icc (0 : ℝ) threeR) :
    Spline.diagonalSplinePotential 3 x = threeCenterPotential x := by
  unfold Spline.diagonalSplinePotential threeCenterPotential
  rw [diagonalSplineDensity_three_center (by simpa only [threeR, one_div] using hx)]

theorem three_potential_eq_outer {x : ℝ} (hx : x ∈ Icc threeR (Real.sqrt (3 : ℝ))) :
    Spline.diagonalSplinePotential 3 x = threeOuterPotential x := by
  unfold Spline.diagonalSplinePotential threeOuterPotential
  rw [diagonalSplineDensity_three_outer (by simpa only [threeR, one_div] using hx)]

theorem three_potential_cut : Spline.diagonalSplinePotential 3 threeR = threeV := by
  unfold Spline.diagonalSplinePotential
  rw [show threeR = (Real.sqrt (3 : ℝ))⁻¹ by simp only [threeR, one_div],
    diagonalSplineDensity_three_at_cut]
  unfold threeV
  rw [← Real.log_inv]
  congr 1
  field_simp

theorem threeV_eq_neg_log_cut : threeV = -Real.log (Real.sqrt (3 : ℝ) / 4) := by
  unfold threeV
  rw [← Real.log_inv]
  congr 1
  field_simp

theorem three_potential_pos {x : ℝ}
    (hx : x ∈ Ioo (-Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ))) :
    0 < Spline.diagonalSplinePotential 3 x := by
  have hq0 := Spline.diagonalSplineDensity_pos 3 (by norm_num) x hx
  have hq1 : Spline.diagonalSplineDensity 3 x < 1 := by
    have h := Spline.diagonalSplineDensity_le 3 (by norm_num) x
    norm_num only [Nat.cast_ofNat] at h
    nlinarith [sqrt_three_sq, sqrt_three_pos]
  exact neg_pos.mpr (Real.log_neg hq0 hq1)

theorem hasDerivAt_threeCenterPotential {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt threeCenterPotential (2 * x / (1 - x ^ 2)) x := by
  have hq : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hk : 3 * Real.sqrt (3 : ℝ) / 8 ≠ 0 := by positivity
  have h := ((((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).const_mul
    (3 * Real.sqrt (3 : ℝ) / 8)).log (mul_ne_zero hk hq)).neg
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ring

theorem hasDerivAt_threeOuterPotential {x : ℝ} (hx : x < Real.sqrt (3 : ℝ)) :
    HasDerivAt threeOuterPotential (2 / (Real.sqrt (3 : ℝ) - x)) x := by
  have hq : Real.sqrt (3 : ℝ) - x ≠ 0 := sub_ne_zero.mpr hx.ne'
  have hk : 3 * Real.sqrt (3 : ℝ) / 16 ≠ 0 := by positivity
  have h := (((((hasDerivAt_const x (Real.sqrt (3 : ℝ))).sub (hasDerivAt_id x)).pow 2).const_mul
    (3 * Real.sqrt (3 : ℝ) / 16)).log (mul_ne_zero hk (pow_ne_zero 2 hq))).neg
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ring

theorem hasDerivAt_three_center_first {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => 2 * y / (1 - y ^ 2))
      (2 * (1 + x ^ 2) / (1 - x ^ 2) ^ 2) x := by
  have hq : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have h := ((hasDerivAt_id x).const_mul 2).div
    ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)) hq
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ring

theorem hasDerivAt_three_outer_first {x : ℝ} (hx : x < Real.sqrt (3 : ℝ)) :
    HasDerivAt (fun y : ℝ => 2 / (Real.sqrt (3 : ℝ) - y))
      (2 / (Real.sqrt (3 : ℝ) - x) ^ 2) x := by
  have hq : Real.sqrt (3 : ℝ) - x ≠ 0 := sub_ne_zero.mpr hx.ne'
  have h := (hasDerivAt_const x (2 : ℝ)).div
    ((hasDerivAt_const x (Real.sqrt (3 : ℝ))).sub (hasDerivAt_id x)) hq
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, id_eq]
    field_simp
    ring

theorem hasDerivAt_diagonalSplinePotential_three_center {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) threeR) :
    HasDerivAt (Spline.diagonalSplinePotential 3) (2 * x / (1 - x ^ 2)) x := by
  have heq : Spline.diagonalSplinePotential 3 =ᶠ[𝓝 x] threeCenterPotential := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact three_potential_eq_center ⟨hy.1.le, hy.2.le⟩
  exact (hasDerivAt_threeCenterPotential
    ⟨by linarith [hx.1], lt_trans hx.2 threeR_lt_one⟩).congr_of_eventuallyEq heq

theorem hasDerivAt_diagonalSplinePotential_three_outer {x : ℝ}
    (hx : x ∈ Ioo threeR (Real.sqrt (3 : ℝ))) :
    HasDerivAt (Spline.diagonalSplinePotential 3) (2 / (Real.sqrt (3 : ℝ) - x)) x := by
  have heq : Spline.diagonalSplinePotential 3 =ᶠ[𝓝 x] threeOuterPotential := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact three_potential_eq_outer ⟨hy.1.le, hy.2.le⟩
  exact (hasDerivAt_threeOuterPotential hx.2).congr_of_eventuallyEq heq

theorem hasDerivAt_deriv_diagonalSplinePotential_three_center {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) threeR) :
    HasDerivAt (deriv (Spline.diagonalSplinePotential 3))
      (2 * (1 + x ^ 2) / (1 - x ^ 2) ^ 2) x := by
  have heq : deriv (Spline.diagonalSplinePotential 3) =ᶠ[𝓝 x]
      (fun y : ℝ => 2 * y / (1 - y ^ 2)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hasDerivAt_diagonalSplinePotential_three_center hy).deriv
  exact (hasDerivAt_three_center_first
    ⟨by linarith [hx.1], lt_trans hx.2 threeR_lt_one⟩).congr_of_eventuallyEq heq

theorem hasDerivAt_deriv_diagonalSplinePotential_three_outer {x : ℝ}
    (hx : x ∈ Ioo threeR (Real.sqrt (3 : ℝ))) :
    HasDerivAt (deriv (Spline.diagonalSplinePotential 3))
      (2 / (Real.sqrt (3 : ℝ) - x) ^ 2) x := by
  have heq : deriv (Spline.diagonalSplinePotential 3) =ᶠ[𝓝 x]
      (fun y : ℝ => 2 / (Real.sqrt (3 : ℝ) - y)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hasDerivAt_diagonalSplinePotential_three_outer hy).deriv
  exact (hasDerivAt_three_outer_first hx.2).congr_of_eventuallyEq heq

theorem contDiffOn_diagonalSplinePotential_three :
    ContDiffOn ℝ 1 (Spline.diagonalSplinePotential 3)
      (Ioo (-Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ))) := by
  intro x hx
  exact (Spline.contDiffAt_diagonalSplinePotential 1 3 (by norm_num) x
    (Spline.diagonalSplineDensity_pos 3 (by norm_num) x hx).ne').contDiffWithinAt

theorem deriv_diagonalSplinePotential_three_cut :
    deriv (Spline.diagonalSplinePotential 3) threeR = Real.sqrt (3 : ℝ) := by
  have hrR : threeR < Real.sqrt (3 : ℝ) := by
    have h := sqrt_three_eq_three_inv
    simp only [threeR, one_div]
    linarith [inv_sqrt_three_pos]
  have hx : threeR ∈ Ioo (-Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ)) :=
    ⟨by linarith [threeR_pos, sqrt_three_pos], hrR⟩
  have hd := (Spline.contDiffAt_diagonalSplinePotential 1 3 (by norm_num) threeR
    (Spline.diagonalSplineDensity_pos 3 (by norm_num) threeR hx).ne').differentiableAt (by norm_num)
  have hp := (hasDerivAt_threeCenterPotential
    (show threeR ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [threeR_pos], threeR_lt_one⟩)).hasDerivWithinAt
      (s := Icc (0 : ℝ) threeR)
  have hactual : HasDerivWithinAt (Spline.diagonalSplinePotential 3)
      (2 * threeR / (1 - threeR ^ 2)) (Icc (0 : ℝ) threeR) threeR := by
    apply hp.congr
    · intro y hy
      exact three_potential_eq_center hy
    · exact three_potential_eq_center ⟨threeR_pos.le, le_rfl⟩
  have hu := uniqueDiffOn_Icc threeR_pos
  have huniq := hu threeR ⟨threeR_pos.le, le_rfl⟩
  have hvalue := (hactual.derivWithin huniq).symm.trans (hd.hasDerivAt.hasDerivWithinAt.derivWithin huniq)
  rw [← hvalue, threeR_sq]
  calc
    _ = 3 * threeR := by ring
    _ = Real.sqrt (3 : ℝ) := by
      simpa only [threeR, one_div] using sqrt_three_eq_three_inv.symm

theorem three_center_second_bound {x : ℝ} (hx : x ∈ Icc (0 : ℝ) threeR) :
    0 ≤ 2 * (1 + x ^ 2) / (1 - x ^ 2) ^ 2 ∧
      2 * (1 + x ^ 2) / (1 - x ^ 2) ^ 2 ≤ 6 := by
  have hx2 : x ^ 2 ≤ 1 / 3 := by nlinarith [threeR_sq, hx.1, hx.2, threeR_pos]
  have hq : 0 < (1 - x ^ 2) ^ 2 := sq_pos_of_pos (by nlinarith)
  constructor
  · positivity
  · apply (div_le_iff₀ hq).mpr
    nlinarith [sq_nonneg (x ^ 2)]

theorem three_outer_second_bound {x : ℝ} (hx : x ∈ Icc threeR (2 * threeR)) :
    0 ≤ 2 / (Real.sqrt (3 : ℝ) - x) ^ 2 ∧
      2 / (Real.sqrt (3 : ℝ) - x) ^ 2 ≤ 6 := by
  have hR : Real.sqrt (3 : ℝ) = 3 * threeR := by simpa only [threeR, one_div] using sqrt_three_eq_three_inv
  have hgap : threeR ≤ Real.sqrt (3 : ℝ) - x := by linarith [hx.2]
  have hq : 0 < (Real.sqrt (3 : ℝ) - x) ^ 2 := sq_pos_of_pos (lt_of_lt_of_le threeR_pos hgap)
  constructor
  · positivity
  · apply (div_le_iff₀ hq).mpr
    nlinarith [threeR_sq, threeR_pos]

end
end ENT.Small
