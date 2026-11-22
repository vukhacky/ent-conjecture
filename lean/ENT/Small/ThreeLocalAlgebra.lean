module

public import ENT.Small.EnclosuresThree

/-! The scalar algebra in the local three-dimensional comparison.
The analytic Taylor inequality is an explicit premise of this lemma; it is
not an entropy theorem until that premise is proved for the actual density. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Small
noncomputable section

theorem three_local_polynomial_margin {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 10) :
    (1 : ℝ) / 60 ≤ 3 / 100 - (9 / 10) * ρ ^ 2 - (27 / 250) * ρ ^ 4 -
      (13 / 700) * ρ - (153 / 200) * ρ ^ 3 := by
  have h2 := pow_le_pow_left₀ hρ0 hρ 2
  have h3 := pow_le_pow_left₀ hρ0 hρ 3
  have h4 := pow_le_pow_left₀ hρ0 hρ 4
  norm_num at h2 h3 h4
  linarith

theorem three_local_algebra {ρ u r R B C e K d p E D : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 10) (hu : u = ρ ^ 2)
    (hr : 0 ≤ r) (hR0 : 0 ≤ R) (hR : R ≤ 7 / 4)
    (hB : 3 / 100 ≤ B + 2 * r / 3) (hC : -10 ≤ C)
    (he0 : 0 ≤ e) (he : e ≤ 27 / 1000) (hK : K ≤ 4)
    (hd : d ≤ -r * u / 2) (hda : |d| ≤ 3 * u / 10)
    (hp : |p| ≤ ρ ^ 3 / 7) (hE : E ≤ 153 * ρ ^ 5 / 200)
    (hD : -4 * d / 3 + B * u + C * d ^ 2 - 2 * e * d * u +
      4 * e * p + K * d ^ 3 +
      R * (u ^ 2 / 3 + d ^ 2 * u - 4 * d * p + d ^ 4 / 8) - E ≤ D) :
    u / 60 ≤ D := by
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu1 : u ≤ 1 / 100 := by
    rw [hu]
    nlinarith
  have hd0 : d ≤ 0 := hd.trans (by nlinarith [mul_nonneg hr hu0])
  have hdlo : -(3 * u / 10) ≤ d := (abs_le.mp hda).1
  have hdsq : d ^ 2 ≤ 9 * u ^ 2 / 100 := by
    have h := pow_le_pow_left₀ (abs_nonneg d) hda 2
    simpa only [sq_abs] using (show d ^ 2 ≤ 9 * u ^ 2 / 100 by nlinarith [h])
  have hdcube : -(27 * u ^ 3 / 1000) ≤ d ^ 3 := by
    have h := pow_le_pow_left₀ (show 0 ≤ -d by linarith)
      (show -d ≤ 3 * u / 10 by linarith) 3
    nlinarith [h]
  have hd3zero : d ^ 3 ≤ 0 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hd0 (sq_nonneg d)]
  have hlead : 3 * u / 100 ≤ -4 * d / 3 + B * u := by
    have h := mul_le_mul_of_nonneg_right hB hu0
    nlinarith
  have hcterm : -(9 * u ^ 2 / 10) ≤ C * d ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hC (sq_nonneg d)
    nlinarith
  have hkterm : -(27 * u ^ 3 / 250) ≤ K * d ^ 3 := by
    have h := mul_le_mul_of_nonpos_right hK hd3zero
    nlinarith
  have htheta0 : 0 ≤ 4 * e - 4 * R * d := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hR0 hd0]
  have htheta : 4 * e - 4 * R * d ≤ 13 / 100 := by
    have h := mul_le_mul hR (show -d ≤ 3 * u / 10 by linarith)
      (show 0 ≤ -d by linarith) (by norm_num : (0 : ℝ) ≤ 7 / 4)
    nlinarith
  have hpterm : -(13 * ρ ^ 3 / 700) ≤ (4 * e - 4 * R * d) * p := by
    have hl := mul_le_mul_of_nonneg_left (abs_le.mp hp).1 htheta0
    have hu' := mul_le_mul_of_nonneg_right htheta
      (show 0 ≤ ρ ^ 3 / 7 by positivity)
    nlinarith
  have hdiscard1 : 0 ≤ -2 * e * d * u := by
    have := mul_nonpos_of_nonneg_of_nonpos he0 hd0
    nlinarith [mul_nonpos_of_nonpos_of_nonneg this hu0]
  have hdiscard2 : 0 ≤ R * (u ^ 2 / 3 + d ^ 2 * u + d ^ 4 / 8) := by
    positivity
  have hbound : u * (3 / 100 - (9 / 10) * ρ ^ 2 - (27 / 250) * ρ ^ 4 -
      (13 / 700) * ρ - (153 / 200) * ρ ^ 3) ≤ D := by
    have hid : u * (3 / 100 - (9 / 10) * ρ ^ 2 - (27 / 250) * ρ ^ 4 -
      (13 / 700) * ρ - (153 / 200) * ρ ^ 3) =
      3 * u / 100 - 9 * u ^ 2 / 10 - 27 * u ^ 3 / 250 -
      13 * ρ ^ 3 / 700 - 153 * ρ ^ 5 / 200 := by rw [hu]; ring
    rw [hid]
    nlinarith only [hD, hlead, hcterm, hkterm, hpterm, hdiscard1, hdiscard2, hE]
  have hmargin := mul_le_mul_of_nonneg_left (three_local_polynomial_margin hρ0 hρ) hu0
  linarith

end
end ENT.Small
