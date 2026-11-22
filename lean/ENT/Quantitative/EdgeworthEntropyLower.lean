module

public import ENT.Quantitative.EdgeworthVariational
public import Mathlib.Analysis.SpecificLimits.Basic

/-! A quantitative lower bound for the Gaussian entropy defect of standardized uniform sums, with leading coefficient 3/100. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace ENT.Quantitative
noncomputable section

theorem diagonalGaussianDefect_quartic_lower {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    6*t/(5*(n:ℝ)) - 12*t^2 - 36*Real.exp 6*t^3 ≤ diagonalGaussianDefect n := by
  let p := standardizedProjectionDensity (diagonal n) (isUnit_diagonal hn)
  let hKL := standardizedProjectionFiniteKL (diagonal n) (isUnit_diagonal hn)
  have hf : Integrable (fun x => p.density x * quarticGaussianTest t x) := by
    have h := (p.integrable_iff_density (quarticGaussianTest t)).mp
      ((integrable_hermite4_projection (diagonal n)).const_mul (-t))
    simpa only [mul_comm] using h
  have hi : (∫ x, p.density x * quarticGaussianTest t x) = 6*t/(5*(n:ℝ)) := by
    have h := p.integral_eq_density (quarticGaussianTest t)
    rw [show (∫ x, quarticGaussianTest t x ∂standardizedProjectionLaw (diagonal n)) =
      -t * (∫ x, hermite4Even.eval (x^2) ∂standardizedProjectionLaw (diagonal n)) by
        exact integral_const_mul _ _, integral_hermite4_diagonal hn] at h
    calc
      _ = -t * (-6 / (5*(n:ℝ))) := by simpa only [mul_comm] using h.symm
      _ = _ := by ring
  have h := FiniteKLData.test_lower_bound hKL (quarticGaussianTest t)
    (fun x => gaussianPDFReal_pos 0 1 x (by norm_num)) hf
    (integrable_quarticGaussianTest_density ht)
  have hZ := quarticGaussianTest_integral_upper ht ht1
  change (∫ x, p.density x * quarticGaussianTest t x) + 1 -
    (∫ x, gaussianPDFReal 0 1 x * Real.exp (quarticGaussianTest t x)) ≤ _ at h
  rw [hi, ← diagonalGaussianDefect_eq_kl hn] at h
  linarith

theorem diagonalGaussianDefect_explicit_lower {n : ℕ} (hn : 0 < n) :
    (3/100:ℝ)/(n:ℝ)^2 - 9*Real.exp 6/(2000*(n:ℝ)^3) ≤ diagonalGaussianDefect n := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have ht : 0 ≤ 1/(20*(n:ℝ)) := by positivity
  have ht1 : 1/(20*(n:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have h := diagonalGaussianDefect_quartic_lower hn ht ht1
  have he : 6*(1/(20*(n:ℝ)))/(5*(n:ℝ)) - 12*(1/(20*(n:ℝ)))^2 -
      36*Real.exp 6*(1/(20*(n:ℝ)))^3 =
      (3/100:ℝ)/(n:ℝ)^2 - 9*Real.exp 6/(2000*(n:ℝ)^3) := by
    field_simp
    ring
  rwa [he] at h

theorem diagonalGaussianDefect_scaled_lower {n : ℕ} (hn : 0 < n) :
    (3/100:ℝ) - (9*Real.exp 6/2000)/(n:ℝ) ≤ (n:ℝ)^2*diagonalGaussianDefect n := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h := mul_le_mul_of_nonneg_left (diagonalGaussianDefect_explicit_lower hn)
    (sq_nonneg (n:ℝ))
  convert h using 1 <;> field_simp <;> ring

/-- The sharp leading *lower* bound, proved without assuming Edgeworth.
This is a liminf statement, not the full entropy asymptotic. -/
theorem eventually_diagonalGaussianDefect_scaled_ge (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (3/100:ℝ) - ε ≤ (n:ℝ)^2*diagonalGaussianDefect n := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ => (9*Real.exp 6/2000)/(n:ℝ)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero, div_eq_mul_inv] using hi.const_mul (9*Real.exp 6/2000)
  filter_upwards [he.eventually (gt_mem_nhds hε), eventually_ge_atTop (1:ℕ)] with n hn hn1
  exact (by linarith : (3/100:ℝ) - ε ≤ (3/100:ℝ) - (9*Real.exp 6/2000)/(n:ℝ)).trans
    (diagonalGaussianDefect_scaled_lower (by omega))

end
end ENT.Quantitative
