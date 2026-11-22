module

public import ENT.Small.Enclosures

/-! Exact rational enclosures for all elementary constants in the local n=3 proof. -/

@[expose] public section

set_option autoImplicit false

open Finset

namespace ENT.Small

noncomputable section

def threeR : ℝ := 1 / Real.sqrt 3
def threeV : ℝ := Real.log (4 / Real.sqrt 3)
def threeH : ℝ := 7 / 6 + 2 * Real.log 2 - (1 / 2) * Real.log 3 -
  Real.sqrt 3 * Real.artanh threeR
def threeJ : ℝ := threeR * threeV + 2 * threeR - 2 * Real.artanh threeR
def threeF2R : ℝ := threeJ + 2 * threeR * (threeV + 2)
def threeB : ℝ := -2 * threeR * threeH + 2 * threeJ
def threeC : ℝ := 12 * threeR * threeH + (3 / 2) * threeJ - (9 / 2) * threeF2R
def threeE : ℝ := threeH - threeV
def threeK : ℝ := 4 * threeH + threeV / 2
def threeScaledArtanh : ℝ := Real.sqrt 3 * Real.artanh threeR
def threeScaledSeries (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (1 / 3 : ℝ) ^ k / ((2 * k + 1 : ℕ) : ℝ)

theorem threeR_pos : 0 < threeR := by unfold threeR; positivity

theorem threeR_sq : threeR ^ 2 = 1 / 3 := by
  unfold threeR
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem threeR_lt_one : threeR < 1 := by nlinarith [threeR_sq, threeR_pos]

theorem sqrt_three_mul_threeR : Real.sqrt 3 * threeR = 1 := by
  unfold threeR
  field_simp

theorem threeR_mul_scaledArtanh : threeR * threeScaledArtanh = Real.artanh threeR := by
  unfold threeScaledArtanh
  calc
    _ = (Real.sqrt 3 * threeR) * Real.artanh threeR := by ring
    _ = _ := by rw [sqrt_three_mul_threeR, one_mul]

theorem threeR_bounds : (577350 : ℝ) / 1000000 ≤ threeR ∧
    threeR ≤ (577351 : ℝ) / 1000000 := by
  constructor <;> nlinarith [threeR_sq, threeR_pos]

theorem log_two_bounds : (69314718055 : ℝ) / 100000000000 ≤ Real.log 2 ∧
    Real.log 2 ≤ (69314718057 : ℝ) / 100000000000 := by
  have h := Enclosures.log_ratio_taylor_bounds (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 12
  norm_num [Enclosures.artanhTaylor, Enclosures.artanhError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem log_three_bounds : (109861228866 : ℝ) / 100000000000 ≤ Real.log 3 ∧
    Real.log 3 ≤ (109861228868 : ℝ) / 100000000000 := by
  have h := Enclosures.log_ratio_taylor_bounds (x := (1 : ℝ) / 2) (by norm_num) (by norm_num) 20
  norm_num [Enclosures.artanhTaylor, Enclosures.artanhError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem three_scaled_monomial (k : ℕ) :
    Real.sqrt 3 * threeR ^ (2 * k + 1) = (1 / 3 : ℝ) ^ k := by
  calc
    _ = (Real.sqrt 3 * threeR) * (threeR ^ 2) ^ k := by
      rw [pow_add, pow_mul, pow_one]
      ring
    _ = _ := by rw [sqrt_three_mul_threeR, threeR_sq, one_mul]

theorem three_scaled_artanhTaylor (n : ℕ) :
    Real.sqrt 3 * Enclosures.artanhTaylor n threeR = threeScaledSeries n := by
  unfold Enclosures.artanhTaylor threeScaledSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_div_assoc, three_scaled_monomial]

theorem three_scaled_artanhError (n : ℕ) :
    Real.sqrt 3 * Enclosures.artanhError n threeR = (3 / 2 : ℝ) * (1 / 3 : ℝ) ^ n := by
  unfold Enclosures.artanhError
  rw [← mul_div_assoc, three_scaled_monomial, threeR_sq]
  ring

theorem threeScaledArtanh_series_bounds (n : ℕ) :
    threeScaledSeries n ≤ threeScaledArtanh ∧
      threeScaledArtanh ≤ threeScaledSeries n + (3 / 2 : ℝ) * (1 / 3 : ℝ) ^ n := by
  have h := Enclosures.artanh_taylor_bounds threeR_pos.le threeR_lt_one n
  have hl := mul_le_mul_of_nonneg_left h.1 (Real.sqrt_nonneg 3)
  have hu := mul_le_mul_of_nonneg_left h.2 (Real.sqrt_nonneg 3)
  rw [three_scaled_artanhTaylor] at hl
  rw [mul_add, three_scaled_artanhTaylor, three_scaled_artanhError] at hu
  exact ⟨hl, hu⟩

theorem threeScaledArtanh_bounds :
    (114051899444 : ℝ) / 100000000000 ≤ threeScaledArtanh ∧
      threeScaledArtanh ≤ (114051899447 : ℝ) / 100000000000 := by
  have h := threeScaledArtanh_series_bounds 24
  have hl : (114051899444 : ℝ) / 100000000000 ≤ threeScaledSeries 24 := by
    norm_num [threeScaledSeries, Finset.sum_range_succ]
  have hu : threeScaledSeries 24 + (3 / 2 : ℝ) * (1 / 3 : ℝ) ^ 24 ≤
      (114051899447 : ℝ) / 100000000000 := by
    norm_num [threeScaledSeries, Finset.sum_range_succ]
  exact ⟨hl.trans h.1, h.2.trans hu⟩

theorem threeV_eq : threeV = 2 * Real.log 2 - (1 / 2 : ℝ) * Real.log 3 := by
  unfold threeV
  rw [Real.log_div (by norm_num) (by positivity), Real.log_sqrt (by norm_num)]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  ring

theorem threeH_eq : threeH = 7 / 6 + threeV - threeScaledArtanh := by
  rw [threeV_eq]
  unfold threeH threeScaledArtanh
  ring

theorem threeV_bounds : (836987 : ℝ) / 1000000 ≤ threeV ∧
    threeV ≤ (836991 : ℝ) / 1000000 := by
  rw [threeV_eq]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, log_three_bounds.1, log_three_bounds.2]

theorem threeH_bounds : (8631358889 : ℝ) / 10000000000 ≤ threeH ∧
    threeH ≤ (8631358891 : ℝ) / 10000000000 := by
  rw [threeH_eq, threeV_eq]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2,
    log_three_bounds.1, log_three_bounds.2, threeScaledArtanh_bounds.1, threeScaledArtanh_bounds.2]

theorem threeB_identity : threeB + 2 * threeR / 3 =
    threeR * (7 / 3 - 2 * threeScaledArtanh) := by
  unfold threeB threeJ
  rw [threeH_eq]
  nlinarith [threeR_mul_scaledArtanh]

theorem threeC_identity : threeC = -threeR * (10 + 6 * threeScaledArtanh) := by
  unfold threeC threeF2R threeJ
  rw [threeH_eq]
  nlinarith [threeR_mul_scaledArtanh]

theorem threeE_identity : threeE = 7 / 6 - threeScaledArtanh := by
  rw [threeE, threeH_eq]
  ring

theorem threeK_identity : threeK = 14 / 3 + (9 / 2 : ℝ) * threeV - 4 * threeScaledArtanh := by
  rw [threeK, threeH_eq]
  ring

theorem threeB_bound : (3 : ℝ) / 100 < threeB + 2 * threeR / 3 := by
  rw [threeB_identity]
  have hc : 7 / 3 - 2 * ((1140520 : ℝ) / 1000000) ≤ 7 / 3 - 2 * threeScaledArtanh := by
    linarith [threeScaledArtanh_bounds.2]
  have h := mul_le_mul threeR_bounds.1 hc (by norm_num) threeR_pos.le
  norm_num at h
  linarith

theorem threeC_bounds : -10 < threeC ∧ threeC < 0 := by
  rw [threeC_identity]
  have hc0 : 0 < 10 + 6 * threeScaledArtanh := by linarith [threeScaledArtanh_bounds.1]
  have hc : 10 + 6 * threeScaledArtanh ≤ 10 + 6 * ((1140520 : ℝ) / 1000000) := by
    linarith [threeScaledArtanh_bounds.2]
  have h := mul_le_mul threeR_bounds.2 hc hc0.le (by norm_num)
  have hp := mul_pos threeR_pos hc0
  norm_num at h
  constructor <;> nlinarith

theorem threeE_bounds : 0 < threeE ∧ threeE < 27 / 1000 := by
  rw [threeE_identity]
  constructor <;> linarith [threeScaledArtanh_bounds.1, threeScaledArtanh_bounds.2]

theorem threeK_bounds : 0 < threeK ∧ threeK < 4 := by
  rw [threeK_identity]
  constructor <;> linarith [threeV_bounds.1, threeV_bounds.2,
    threeScaledArtanh_bounds.1, threeScaledArtanh_bounds.2]

/-- All four scalar inequalities displayed in the manuscript's n=3 appendix. -/
theorem three_scalar_bounds :
    (3 : ℝ) / 100 < threeB + 2 * threeR / 3 ∧
      (-10 < threeC ∧ threeC < 0) ∧ (0 < threeE ∧ threeE < 27 / 1000) ∧
      (0 < threeK ∧ threeK < 4) :=
  ⟨threeB_bound, threeC_bounds, threeE_bounds, threeK_bounds⟩

end
end ENT.Small
