module

public import ENT.Small.EnclosuresLogCertificate
public import ENT.Small.FourConstantsCoordinates
public import ENT.Small.LogQuadratureData.J24Batch000
public import ENT.Small.LogQuadratureData.J34Batch000

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace ENT.Small
noncomputable section
open Spline Quadrature Certificate

theorem unitSumSplineDensity_four_inner (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    unitSumSplineDensity 4 (1+x) = rationalPolynomial [1,3,3,-3] 6 x := by
  have h := unitSumSplineDensity_eq_rationalPolynomial 4 1 (by decide) (by decide) x hx.1 hx.2
  have hc : splineCoeffs 4 1 = [1,3,3,-3] := by decide +kernel
  have hd : (Nat.factorial (4-1):ℤ) = 6 := by norm_num
  rw [hc,hd] at h
  simpa only [Nat.cast_one] using h

theorem continuousOn_log_unitSum_four_inner :
    ContinuousOn (fun x : ℝ => Real.log (unitSumSplineDensity 4 (1+x))) (Icc 0 1) := by
  apply ((continuous_unitSumSplineDensity 4).comp (continuous_const.add continuous_id)).continuousOn.log
  intro x hx
  exact (unitSumSplineDensity_pos 4 (by decide) (1+x) (by linarith [hx.1]) (by norm_num only [Nat.cast_ofNat]; linarith [hx.2])).ne'

theorem fourJ2_bounds : (31413180/100000000:ℝ) ≤ fourJ2 ∧ fourJ2 ≤ (31413182/100000000:ℝ) := by
  have hc : ContinuousOn (fun x : ℝ => -x*Real.log (unitSumSplineDensity 4 (1+x))) (Icc 0 1) :=
    (by fun_prop : Continuous (fun x : ℝ => -x)).continuousOn.mul continuousOn_log_unitSum_four_inner
  have hi : IntervalIntegrable (fun x : ℝ => -x*Real.log (unitSumSplineDensity 4 (1+x))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)]
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have his (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      IntervalIntegrable (fun x : ℝ => -x*Real.log (unitSumSplineDensity 4 (1+x))) volume a b := hi.mono_set (by
    rw [uIcc_of_le hab,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc ha hb)
  have h0 := LogQuadratureCell.transfer Certified.J24Cell000 Certified.J24Cell000_valid
    (fun x : ℝ => unitSumSplineDensity 4 (1+x)) (fun x : ℝ => -x)
    (by
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 1 := by
        norm_num only [Certified.J24Cell000,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at hx
        constructor <;> linarith [hx.1,hx.2]
      exact unitSumSplineDensity_four_inner x hx')
    (by
      intro x hx
      norm_num [Certified.J24Cell000,rationalPolynomial,eval,List.foldr])
  norm_num only [Certified.J24Cell000,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,neg_one_mul] at h0
  rcases h0 with ⟨hl0,hu0⟩
  have h1 := LogQuadratureCell.transfer Certified.J24Cell001 Certified.J24Cell001_valid
    (fun x : ℝ => unitSumSplineDensity 4 (1+x)) (fun x : ℝ => -x)
    (by
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 1 := by
        norm_num only [Certified.J24Cell001,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at hx
        constructor <;> linarith [hx.1,hx.2]
      exact unitSumSplineDensity_four_inner x hx')
    (by
      intro x hx
      norm_num [Certified.J24Cell001,rationalPolynomial,eval,List.foldr])
  norm_num only [Certified.J24Cell001,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,neg_one_mul] at h1
  rcases h1 with ⟨hl1,hu1⟩
  have h2 := LogQuadratureCell.transfer Certified.J24Cell002 Certified.J24Cell002_valid
    (fun x : ℝ => unitSumSplineDensity 4 (1+x)) (fun x : ℝ => -x)
    (by
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 1 := by
        norm_num only [Certified.J24Cell002,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at hx
        constructor <;> linarith [hx.1,hx.2]
      exact unitSumSplineDensity_four_inner x hx')
    (by
      intro x hx
      norm_num [Certified.J24Cell002,rationalPolynomial,eval,List.foldr])
  norm_num only [Certified.J24Cell002,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,neg_one_mul] at h2
  rcases h2 with ⟨hl2,hu2⟩
  have h3 := LogQuadratureCell.transfer Certified.J24Cell003 Certified.J24Cell003_valid
    (fun x : ℝ => unitSumSplineDensity 4 (1+x)) (fun x : ℝ => -x)
    (by
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 1 := by
        norm_num only [Certified.J24Cell003,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at hx
        constructor <;> linarith [hx.1,hx.2]
      exact unitSumSplineDensity_four_inner x hx')
    (by
      intro x hx
      norm_num [Certified.J24Cell003,rationalPolynomial,eval,List.foldr])
  norm_num only [Certified.J24Cell003,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,neg_one_mul] at h3
  rcases h3 with ⟨hl3,hu3⟩
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (his 0 (11/64:ℝ) (by norm_num) (by norm_num) (by norm_num)) (his (11/64:ℝ) (25/64:ℝ) (by norm_num) (by norm_num) (by norm_num))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (his 0 (25/64:ℝ) (by norm_num) (by norm_num) (by norm_num)) (his (25/64:ℝ) (43/64:ℝ) (by norm_num) (by norm_num) (by norm_num))
  have hs3 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (his 0 (43/64:ℝ) (by norm_num) (by norm_num) (by norm_num)) (his (43/64:ℝ) 1 (by norm_num) (by norm_num) (by norm_num))
  rw [fourJ2_eq_unitSum_log_integral]
  constructor <;> linarith

theorem fourJ3_bounds : (85437851/100000000:ℝ) ≤ fourJ3 ∧ fourJ3 ≤ (85437853/100000000:ℝ) := by
  have hc : ContinuousOn (fun x : ℝ => (-1:ℝ)*Real.log (unitSumSplineDensity 4 (1+x))) (Icc 0 1) :=
    (by fun_prop : Continuous (fun x : ℝ => (-1:ℝ))).continuousOn.mul continuousOn_log_unitSum_four_inner
  have hi : IntervalIntegrable (fun x : ℝ => (-1:ℝ)*Real.log (unitSumSplineDensity 4 (1+x))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)]
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have his (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      IntervalIntegrable (fun x : ℝ => (-1:ℝ)*Real.log (unitSumSplineDensity 4 (1+x))) volume a b := hi.mono_set (by
    rw [uIcc_of_le hab,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc ha hb)
  have h0 := LogQuadratureCell.transfer Certified.J34Cell000 Certified.J34Cell000_valid
    (fun x : ℝ => unitSumSplineDensity 4 (1+x)) (fun x : ℝ => (-1:ℝ))
    (by
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 1 := by
        norm_num only [Certified.J34Cell000,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at hx
        constructor <;> linarith [hx.1,hx.2]
      exact unitSumSplineDensity_four_inner x hx')
    (by
      intro x hx
      norm_num [Certified.J34Cell000,rationalPolynomial,eval,List.foldr])
  norm_num only [Certified.J34Cell000,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,neg_one_mul] at h0
  rcases h0 with ⟨hl0,hu0⟩
  have h1 := LogQuadratureCell.transfer Certified.J34Cell001 Certified.J34Cell001_valid
    (fun x : ℝ => unitSumSplineDensity 4 (1+x)) (fun x : ℝ => (-1:ℝ))
    (by
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 1 := by
        norm_num only [Certified.J34Cell001,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at hx
        constructor <;> linarith [hx.1,hx.2]
      exact unitSumSplineDensity_four_inner x hx')
    (by
      intro x hx
      norm_num [Certified.J34Cell001,rationalPolynomial,eval,List.foldr])
  norm_num only [Certified.J34Cell001,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,neg_one_mul] at h1
  rcases h1 with ⟨hl1,hu1⟩
  have h2 := LogQuadratureCell.transfer Certified.J34Cell002 Certified.J34Cell002_valid
    (fun x : ℝ => unitSumSplineDensity 4 (1+x)) (fun x : ℝ => (-1:ℝ))
    (by
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 1 := by
        norm_num only [Certified.J34Cell002,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at hx
        constructor <;> linarith [hx.1,hx.2]
      exact unitSumSplineDensity_four_inner x hx')
    (by
      intro x hx
      norm_num [Certified.J34Cell002,rationalPolynomial,eval,List.foldr])
  norm_num only [Certified.J34Cell002,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,neg_one_mul] at h2
  rcases h2 with ⟨hl2,hu2⟩
  have h3 := LogQuadratureCell.transfer Certified.J34Cell003 Certified.J34Cell003_valid
    (fun x : ℝ => unitSumSplineDensity 4 (1+x)) (fun x : ℝ => (-1:ℝ))
    (by
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 1 := by
        norm_num only [Certified.J34Cell003,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at hx
        constructor <;> linarith [hx.1,hx.2]
      exact unitSumSplineDensity_four_inner x hx')
    (by
      intro x hx
      norm_num [Certified.J34Cell003,rationalPolynomial,eval,List.foldr])
  norm_num only [Certified.J34Cell003,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,neg_one_mul] at h3
  rcases h3 with ⟨hl3,hu3⟩
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (his 0 (11/64:ℝ) (by norm_num) (by norm_num) (by norm_num)) (his (11/64:ℝ) (25/64:ℝ) (by norm_num) (by norm_num) (by norm_num))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (his 0 (25/64:ℝ) (by norm_num) (by norm_num) (by norm_num)) (his (25/64:ℝ) (43/64:ℝ) (by norm_num) (by norm_num) (by norm_num))
  have hs3 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (his 0 (43/64:ℝ) (by norm_num) (by norm_num) (by norm_num)) (his (43/64:ℝ) 1 (by norm_num) (by norm_num) (by norm_num))
  rw [fourJ3_eq_unitSum_log_integral]
  simp only [neg_one_mul] at hs1 hs2 hs3
  constructor <;> linarith

end
end ENT.Small
