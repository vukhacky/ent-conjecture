module

public import ENT.Quantitative.EntropyExpansionComplete
public import ENT.Quantitative.SharpnessReduction

/-! Entropic Edgeworth expansion for normalized sums of continuous uniform random variables. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ENT.Quantitative
noncomputable section

/-- The formerly conditional Edgeworth interface now has a closed witness. -/
theorem uniformEntropicEdgeworth_proved : UniformEntropicEdgeworth :=
  ⟨9/250, diagonalGaussianDefect_third_order_expansion⟩

theorem diagonalGaussianDefect_cubic_coefficient :
    Tendsto (fun n : ℕ => (n:ℝ)^3*(diagonalGaussianDefect n-(3/100:ℝ)/(n:ℝ)^2))
      atTop (𝓝 (9/250:ℝ)) := by
  have h := diagonalGaussianDefect_third_order_expansion.add_const (9/250:ℝ)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  ring

theorem diagonalGaussianDefect_leading_coefficient :
    Tendsto (fun n : ℕ => (n:ℝ)^2*diagonalGaussianDefect n) atTop (𝓝 (3/100:ℝ)) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (diagonalGaussianDefect_cubic_coefficient.mul hi).add_const (3/100:ℝ)
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  ring

theorem diagonalGaussianDefect_tendsto_zero :
    Tendsto diagonalGaussianDefect atTop (𝓝 (0:ℝ)) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := diagonalGaussianDefect_leading_coefficient.mul (hi.pow 2)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

theorem diagonalEntropy_gaussian_limit :
    Tendsto diagonalEntropy atTop
      (𝓝 (Real.log (Real.sqrt (2*Real.pi))+1/2-Real.log (Real.sqrt 3))) := by
  have h := diagonalGaussianDefect_tendsto_zero.const_sub
    (Real.log (Real.sqrt (2*Real.pi))+1/2-Real.log (Real.sqrt 3))
  simp only [sub_zero] at h
  convert h using 1
  funext n
  unfold diagonalGaussianDefect
  ring

theorem adjacent_entropy_gap_tendsto :
    Tendsto (fun n : ℕ => (n+1:ℝ)^2*(n:ℝ)*(diagonalEntropy (n+1)-diagonalEntropy n))
      atTop (𝓝 (3/50:ℝ)) :=
  adjacent_entropy_gap_tendsto_of_edgeworth uniformEntropicEdgeworth_proved

end
end ENT.Quantitative
