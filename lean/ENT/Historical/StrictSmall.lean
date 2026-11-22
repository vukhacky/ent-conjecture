module

public import ENT.Small.EnclosuresFiveSix
public import ENT.Small.RemainderFive
public import ENT.Small.RemainderSix

/-! Strict lower bounds for the local curvature constants and strict upper bounds on averaged Taylor remainders in dimensions five and six. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Small
noncomputable section

theorem smallKappa_five_explicit_lower :
    (33460578161 / 1200000000000 : ℝ) ≤ smallKappa 5 := by
  have he := smallKappa_formula_half 5 (by decide)
  norm_num at he
  rw [log_twentyfour_eq] at he
  linarith [kappa_middle_5_bounds.2, log_two_bounds.2, log_three_bounds.2]

theorem smallKappa_five_strict : (27 / 1000 : ℝ) < smallKappa 5 := by
  linarith [smallKappa_five_explicit_lower]

theorem smallKappa_six_explicit_lower :
    (164708417371 / 9000000000000 : ℝ) ≤ smallKappa 6 := by
  have he := smallKappa_formula_half 6 (by decide)
  norm_num at he
  rw [log_onehundredtwenty_eq] at he
  linarith [kappa_middle_6_bounds.2, log_two_bounds.2, log_three_bounds.2, log_five_bounds.2]

theorem smallKappa_six_strict : (17 / 1000 : ℝ) < smallKappa 6 := by
  linarith [smallKappa_six_explicit_lower]

open PureRemainder PureRemainder.Certified

theorem logThirdEnvelope_five_strict :
    ∃ H : LogThirdEnvelope 5 (29 / 500 : ℝ),
      averagedRemainderBound 5 H.bound < (77 / 10 : ℝ) := by
  let U : ℚ := 2 * (8 / (1 - (29 / 500 : ℚ)) ^ 3) * (1 / (5 * 24 * 2 ^ 5) : ℚ) +
    2 * (∑ i : Fin 128, (M5Step i).bound * (M5Area i).area)
  have hU : U < (77 / 10 : ℚ) := M5Numeric
  have h := remainderBound_from_pure_grid 5 (by decide) 128
    M5DerivativeGrid M5DerivativeGrid_valid rfl
    (29 / 500) (by norm_num) 8 (by norm_num)
    (fun v hv => logThirdUnitSum_five_outer hv)
    M5Step M5Area M5Step_valid M5Area_valid M5Geometry
    (by norm_num) U (by
      simpa only [show Nat.factorial 4 = 24 from rfl, Nat.cast_ofNat] using le_refl U)
  have hγ : ((29 / 500 : ℚ) : ℝ) = (29 / 500 : ℝ) := by norm_num
  rw [hγ] at h
  obtain ⟨H, hH⟩ := h
  refine ⟨H, lt_of_le_of_lt hH ?_⟩
  have hc : (U : ℝ) < ((77 / 10 : ℚ) : ℝ) := Rat.cast_lt.mpr hU
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
  exact hc

theorem logThirdEnvelope_six_strict :
    ∃ H : LogThirdEnvelope 6 (1 / 25 : ℝ),
      averagedRemainderBound 6 H.bound < (13 / 2 : ℝ) := by
  let U : ℚ := 2 * (10 / (1 - (1 / 25 : ℚ)) ^ 3) * (1 / (6 * 120 * 2 ^ 6) : ℚ) +
    2 * (∑ i : Fin 160, (M6Step i).bound * (M6Area i).area)
  have hU : U < (13 / 2 : ℚ) := M6Numeric
  have h := remainderBound_from_pure_grid 6 (by decide) 160
    M6DerivativeGrid M6DerivativeGrid_valid rfl
    (1 / 25) (by norm_num) 10 (by norm_num)
    (fun v hv => logThirdUnitSum_six_outer hv)
    M6Step M6Area M6Step_valid M6Area_valid M6Geometry
    (by norm_num) U (by
      simpa only [show Nat.factorial 5 = 120 from rfl, Nat.cast_ofNat] using le_refl U)
  have hγ : ((1 / 25 : ℚ) : ℝ) = (1 / 25 : ℝ) := by norm_num
  rw [hγ] at h
  obtain ⟨H, hH⟩ := h
  refine ⟨H, lt_of_le_of_lt hH ?_⟩
  have hc : (U : ℝ) < ((13 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr hU
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
  exact hc

end
end ENT.Small
