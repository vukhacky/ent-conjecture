module

public import ENT.Small.Enclosures

/-! Algebraic bounds for the local Taylor comparison in dimension four. -/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ENT.Small
noncomputable section

theorem four_local_polynomial_margin {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 20) :
    (1 : ℝ) / 200 ≤ 11 / 1000 - (393 / 500) * ρ ^ 2 - (167 / 500) * ρ ^ 4 -
      (1 / 50) * ρ - (6 / 5) * ρ ^ 3 := by
  have h2 := pow_le_pow_left₀ hρ0 hρ 2
  have h3 := pow_le_pow_left₀ hρ0 hρ 3
  have h4 := pow_le_pow_left₀ hρ0 hρ 4
  norm_num at h2 h3 h4
  linarith

theorem four_local_algebra {ρ u B C e K d s₃ s₄ h v F E D : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 20) (hu : u = ρ ^ 2)
    (hB : 11 / 1000 ≤ 1 / 4 + B) (hC : -10 ≤ C)
    (he0 : 0 ≤ e) (he : e ≤ 13 / 1000) (hK : K ≤ 19)
    (hh : 86 / 100 ≤ h) (hvh0 : 0 ≤ v - h)
    (hvh : (8 / 3 : ℝ) * (v - h) ≤ 5 / 2)
    (hquartic : -54 / 100 ≤ (2 / 3 : ℝ) * v - 2 * h)
    (hd : d ≤ -u / 4) (hda : |d| ≤ 13 * u / 50)
    (hs3 : |s₃| ≤ ρ ^ 3) (hs40 : 0 ≤ s₄) (hs4 : s₄ ≤ u ^ 2)
    (hF : F ≤ (421 / 1000 : ℝ) * u ^ 2) (hE : E ≤ (6 / 5 : ℝ) * ρ ^ 5)
    (hD : -d + B * u + C * d ^ 2 - 4 * e * d * u +
      (4 / 3 : ℝ) * e * s₃ + K * d ^ 3 + 4 * (v - h) * d ^ 2 * u +
      (8 / 3 : ℝ) * (h - v) * d * s₃ + (8 * h + (8 / 3 : ℝ) * v) * d ^ 4 +
      h * u ^ 2 + ((2 / 3 : ℝ) * v - 2 * h) * s₄ - F - E ≤ D) :
    u / 200 ≤ D := by
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu1 : u ≤ 1 / 400 := by rw [hu]; nlinarith
  have hd0 : d ≤ 0 := by linarith
  have hdlo : -(13 * u / 50) ≤ d := (abs_le.mp hda).1
  have hdsq : d ^ 2 ≤ 169 * u ^ 2 / 2500 := by
    have h := pow_le_pow_left₀ (abs_nonneg d) hda 2
    rw [sq_abs] at h
    nlinarith only [h]
  have hdcube : -(2197 * u ^ 3 / 125000) ≤ d ^ 3 := by
    have h := pow_le_pow_left₀ (show 0 ≤ -d by linarith)
      (show -d ≤ 13 * u / 50 by linarith) 3
    nlinarith only [h]
  have hd3zero : d ^ 3 ≤ 0 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hd0 (sq_nonneg d)]
  have hlead : 11 * u / 1000 ≤ -d + B * u := by
    have hb := mul_le_mul_of_nonneg_right hB hu0
    nlinarith only [hb, hd]
  have hcterm : -(169 * u ^ 2 / 250) ≤ C * d ^ 2 := by
    have hc := mul_le_mul_of_nonneg_right hC (sq_nonneg d)
    nlinarith only [hc, hdsq]
  have hkterm : -(167 * u ^ 3 / 500) ≤ K * d ^ 3 := by
    have hk := mul_le_mul_of_nonpos_right hK hd3zero
    nlinarith only [hk, hdcube, pow_nonneg hu0 3]
  let θ := (4 / 3 : ℝ) * e + (8 / 3 : ℝ) * (h - v) * d
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    nlinarith only [he0, mul_nonpos_of_nonneg_of_nonpos hvh0 hd0]
  have hθ : θ ≤ 1 / 50 := by
    have hprod := mul_le_mul hvh (show -d ≤ 13 * u / 50 by linarith)
      (show 0 ≤ -d by linarith) (by norm_num : (0 : ℝ) ≤ 5 / 2)
    dsimp [θ]
    nlinarith only [hprod, he, hu1]
  have hs3term : -(ρ ^ 3 / 50) ≤ θ * s₃ := by
    have hl := mul_le_mul_of_nonneg_left (abs_le.mp hs3).1 hθ0
    have hupper := mul_le_mul_of_nonneg_right hθ (show 0 ≤ ρ ^ 3 by positivity)
    nlinarith only [hl, hupper]
  have hquart : -(11 * u ^ 2 / 100) ≤
      h * u ^ 2 + ((2 / 3 : ℝ) * v - 2 * h) * s₄ - F := by
    have h1 := mul_le_mul_of_nonneg_right hh (sq_nonneg u)
    have h2 := mul_le_mul_of_nonneg_right hquartic hs40
    nlinarith only [h1, h2, hs4, hF, sq_nonneg u]
  have hdiscard1 : 0 ≤ -4 * e * d * u := by
    have := mul_nonpos_of_nonneg_of_nonpos he0 hd0
    nlinarith only [mul_nonpos_of_nonpos_of_nonneg this hu0]
  have hdiscard2 : 0 ≤ 4 * (v - h) * d ^ 2 * u := by positivity
  have hdiscard3 : 0 ≤ (8 * h + (8 / 3 : ℝ) * v) * d ^ 4 := by
    have hh0 : 0 ≤ h := by linarith
    have hv0 : 0 ≤ v := by linarith
    positivity
  have hbound : u * (11 / 1000 - (393 / 500) * ρ ^ 2 - (167 / 500) * ρ ^ 4 -
      (1 / 50) * ρ - (6 / 5) * ρ ^ 3) ≤ D := by
    have hid : u * (11 / 1000 - (393 / 500) * ρ ^ 2 - (167 / 500) * ρ ^ 4 -
      (1 / 50) * ρ - (6 / 5) * ρ ^ 3) =
      11 * u / 1000 - 393 * u ^ 2 / 500 - 167 * u ^ 3 / 500 -
      ρ ^ 3 / 50 - (6 / 5 : ℝ) * ρ ^ 5 := by rw [hu]; ring
    rw [hid]
    dsimp [θ] at hs3term
    nlinarith only [hD, hlead, hcterm, hkterm, hs3term, hquart,
      hdiscard1, hdiscard2, hdiscard3, hE]
  have hmargin := mul_le_mul_of_nonneg_left (four_local_polynomial_margin hρ0 hρ) hu0
  linarith only [hmargin, hbound]

end
end ENT.Small
