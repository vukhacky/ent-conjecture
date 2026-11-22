module

public import ENT.Pang.Tilt

/-! Coefficient positivity for the power series used in Pang's fifth-moment bound. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Pang

noncomputable section

def tiltFourthCumulant (t : ℝ) : ℝ :=
  6 / t ^ 4 - 4 / Real.sinh t ^ 2 - 6 / Real.sinh t ^ 4

def tiltFifthCumulant (t : ℝ) : ℝ :=
  -(24 / t ^ 5) + 8 * Real.cosh t / Real.sinh t ^ 3 +
    24 * Real.cosh t / Real.sinh t ^ 5

theorem fifth_cumulant_gap_identity {t : ℝ} (ht : 0 < t) :
    t ^ 3 * Real.sinh t ^ 5 *
        (tiltFifthCumulant t - 12 * tiltVariance t * tiltThirdCumulant t) =
      8 * t * (t ^ 2 - 3) * Real.cosh t * Real.sinh t ^ 2 +
        48 * t ^ 3 * Real.cosh t - 24 * Real.sinh t ^ 3 := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  unfold tiltFifthCumulant tiltVariance tiltThirdCumulant
  field_simp [ht.ne', hs]
  <;> ring

theorem fifth_ratio_lt_twentyTwo {v k3 k5 : ℝ}
    (hv : 0 < v) (hk3 : k3 < 0) (hgap : 0 < k5 - 12 * v * k3) :
    10 + k5 / (v * k3) < 22 := by
  have hden : v * k3 < 0 := mul_neg_of_pos_of_neg hv hk3
  have hratio : k5 / (v * k3) < 12 := by
    apply (div_lt_iff_of_neg hden).mpr
    nlinarith
  linarith

/-- The algebraic coefficient identity used in Appendix A, equation (65). -/
theorem fifth_coefficient_identity (k : ℝ) :
    2 * k ^ 3 - 14 * k - 27 =
      45 + 2 * (k - 4) * (k ^ 2 + 4 * k + 9) := by
  ring

/-- Positivity of every coefficient in Pang's positive series, before it is
connected to the analytic function by a separate series identity. -/
theorem fifth_series_coefficient_pos (k : ℕ) (hk : 4 ≤ k) :
    0 < (9 : ℝ) ^ (k - 1) *
        (2 * (k : ℝ) ^ 3 - 14 * (k : ℝ) - 27) +
      46 * (k : ℝ) ^ 3 - 10 * (k : ℝ) + 3 := by
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hbase : 0 < 2 * (k : ℝ) ^ 3 - 14 * (k : ℝ) - 27 := by
    rw [fifth_coefficient_identity]
    have hprod : 0 ≤ 2 * ((k : ℝ) - 4) * ((k : ℝ) ^ 2 + 4 * k + 9) := by
      apply mul_nonneg
      · nlinarith
      · positivity
    linarith
  have htail : 0 < 46 * (k : ℝ) ^ 3 - 10 * (k : ℝ) + 3 := by
    have hsq : 0 ≤ 46 * (k : ℝ) ^ 2 - 10 := by nlinarith
    have hm := mul_nonneg hk0 hsq
    nlinarith
  have hm : 0 < (9 : ℝ) ^ (k - 1) *
      (2 * (k : ℝ) ^ 3 - 14 * (k : ℝ) - 27) := mul_pos (by positivity) hbase
  nlinarith

end
end ENT.Pang
