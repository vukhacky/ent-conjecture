module

public import ENT.Small.QuadratureOctic
public import ENT.Small.QuadratureData.W3Batch000

/-! Kernel-checked finite quadrature and analytic tails for the actual W3 partition integral. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace ENT.Small
noncomputable section
open Quadrature

theorem partitionFunction_W3_upper : partitionFunction W3 ≤ (133047/50000:ℝ) := by
  have hf : Continuous (fun x => Real.exp (-W3 x)) := by unfold W3 octicPolynomial; fun_prop
  have h0 : (∫ x in 0..(67/32:ℝ), Real.exp (-W3 x)) ≤ (46429548607979179/36028797018963968:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell000 W3IntegerCoeffs W3Denominator
      Certified.W3Cell000_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell000, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h1 : (∫ x in (67/32:ℝ)..(21/8:ℝ), Real.exp (-W3 x)) ≤ (1406380761120491/36028797018963968:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell001 W3IntegerCoeffs W3Denominator
      Certified.W3Cell001_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell001, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h2 : (∫ x in (21/8:ℝ)..(91/32:ℝ), Real.exp (-W3 x)) ≤ (44285888323425/18014398509481984:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell002 W3IntegerCoeffs W3Denominator
      Certified.W3Cell002_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell002, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h3 : (∫ x in (91/32:ℝ)..(95/32:ℝ), Real.exp (-W3 x)) ≤ (273984767733/1125899906842624:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell003 W3IntegerCoeffs W3Denominator
      Certified.W3Cell003_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell003, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h4 : (∫ x in (95/32:ℝ)..(49/16:ℝ), Real.exp (-W3 x)) ≤ (1296021076961/36028797018963968:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell004 W3IntegerCoeffs W3Denominator
      Certified.W3Cell004_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell004, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h5 : (∫ x in (49/16:ℝ)..(25/8:ℝ), Real.exp (-W3 x)) ≤ (23509493741/4503599627370496:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell005 W3IntegerCoeffs W3Denominator
      Certified.W3Cell005_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell005, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h6 : (∫ x in (25/8:ℝ)..(51/16:ℝ), Real.exp (-W3 x)) ≤ (45529775655/36028797018963968:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell006 W3IntegerCoeffs W3Denominator
      Certified.W3Cell006_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell006, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h7 : (∫ x in (51/16:ℝ)..(13/4:ℝ), Real.exp (-W3 x)) ≤ (1076486643/4503599627370496:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell007 W3IntegerCoeffs W3Denominator
      Certified.W3Cell007_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell007, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h8 : (∫ x in (13/4:ℝ)..(105/32:ℝ), Real.exp (-W3 x)) ≤ (913712665/36028797018963968:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell008 W3IntegerCoeffs W3Denominator
      Certified.W3Cell008_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell008, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h9 : (∫ x in (105/32:ℝ)..(53/16:ℝ), Real.exp (-W3 x)) ≤ (156349165/18014398509481984:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell009 W3IntegerCoeffs W3Denominator
      Certified.W3Cell009_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell009, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h10 : (∫ x in (53/16:ℝ)..(107/32:ℝ), Real.exp (-W3 x)) ≤ (49055875/18014398509481984:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell010 W3IntegerCoeffs W3Denominator
      Certified.W3Cell010_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell010, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h11 : (∫ x in (107/32:ℝ)..(27/8:ℝ), Real.exp (-W3 x)) ≤ (28051711/36028797018963968:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell011 W3IntegerCoeffs W3Denominator
      Certified.W3Cell011_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell011, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h12 : (∫ x in (27/8:ℝ)..(109/32:ℝ), Real.exp (-W3 x)) ≤ (1815513/9007199254740992:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell012 W3IntegerCoeffs W3Denominator
      Certified.W3Cell012_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell012, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h13 : (∫ x in (109/32:ℝ)..(55/16:ℝ), Real.exp (-W3 x)) ≤ (422697/9007199254740992:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell013 W3IntegerCoeffs W3Denominator
      Certified.W3Cell013_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell013, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h14 : (∫ x in (55/16:ℝ)..(111/32:ℝ), Real.exp (-W3 x)) ≤ (43941/4503599627370496:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell014 W3IntegerCoeffs W3Denominator
      Certified.W3Cell014_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell014, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have h15 : (∫ x in (111/32:ℝ)..(7/2:ℝ), Real.exp (-W3 x)) ≤ (64777/36028797018963968:ℝ) := by
    have h := QuadratureCell.sound Certified.W3Cell015 W3IntegerCoeffs W3Denominator
      Certified.W3Cell015_valid W3_rational_monotoneOn
    rw [← W3_eq_rationalPolynomial] at h
    norm_num only [Certified.W3Cell015, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one] at h
    exact h
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (67/32:ℝ)) (hf.intervalIntegrable (67/32:ℝ) (21/8:ℝ))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (21/8:ℝ)) (hf.intervalIntegrable (21/8:ℝ) (91/32:ℝ))
  have hs3 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (91/32:ℝ)) (hf.intervalIntegrable (91/32:ℝ) (95/32:ℝ))
  have hs4 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (95/32:ℝ)) (hf.intervalIntegrable (95/32:ℝ) (49/16:ℝ))
  have hs5 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (49/16:ℝ)) (hf.intervalIntegrable (49/16:ℝ) (25/8:ℝ))
  have hs6 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (25/8:ℝ)) (hf.intervalIntegrable (25/8:ℝ) (51/16:ℝ))
  have hs7 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (51/16:ℝ)) (hf.intervalIntegrable (51/16:ℝ) (13/4:ℝ))
  have hs8 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (13/4:ℝ)) (hf.intervalIntegrable (13/4:ℝ) (105/32:ℝ))
  have hs9 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (105/32:ℝ)) (hf.intervalIntegrable (105/32:ℝ) (53/16:ℝ))
  have hs10 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (53/16:ℝ)) (hf.intervalIntegrable (53/16:ℝ) (107/32:ℝ))
  have hs11 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (107/32:ℝ)) (hf.intervalIntegrable (107/32:ℝ) (27/8:ℝ))
  have hs12 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (27/8:ℝ)) (hf.intervalIntegrable (27/8:ℝ) (109/32:ℝ))
  have hs13 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (109/32:ℝ)) (hf.intervalIntegrable (109/32:ℝ) (55/16:ℝ))
  have hs14 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (55/16:ℝ)) (hf.intervalIntegrable (55/16:ℝ) (111/32:ℝ))
  have hs15 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (111/32:ℝ)) (hf.intervalIntegrable (111/32:ℝ) (7/2:ℝ))
  have ht := W3_tail_integral_le
  rw [partitionFunction_W3_split]
  linarith

end
end ENT.Small
