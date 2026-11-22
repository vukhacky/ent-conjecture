module

public import ENT.Quantitative.EntropyExpansionCentral
public import ENT.Quantitative.EdgeworthEntropyProfileTail

/-! Entropic Edgeworth expansion from the uniform density expansion, the Gaussian envelope, and the entropy Taylor and tail estimates. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory Polynomial Filter
open scoped Topology
namespace ENT.Quantitative
noncomputable section

/-- The actual entropy integral differs from its cubic density profile by
`o(n⁻³)`. Both integrals have independently proved integrability. -/
theorem standardizedDiagonal_gibbs_profile_error_tendsto :
    Tendsto (fun n : ℕ=>(n:ℝ)^3*(diagonalGaussianDefect n-
      ∫x,uniformEdgeworthEntropyProfile n x)) atTop (𝓝 0) := by
  have hc := standardizedDiagonal_gibbs_central_error_tendsto
    uniformDensityEdgeworthBound_proved profileMajorantPolynomial
    profileMajorantPolynomial_nonneg (fun n hn=>profile_abs_le_majorant hn)
  have ht := (hc.add standardizedDiagonal_gibbs_tail_tendsto).sub
    uniformEdgeworthEntropyProfile_tail_tendsto
  simp only [zero_add,sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  have hpart := integral_difference_central_tail
    (integrable_standardizedDiagonal_gibbs hn) (integrable_uniformEdgeworthEntropyProfile n)
    (measurableSet_entropyCentralSet n)
  rw [integral_standardizedDiagonal_gibbs hn] at hpart
  rw [hpart]
  ring

/-- Closed entropic Edgeworth expansion, including the exact third coefficient.
The logarithm is natural and `diagonalGaussianDefect` has been identified
with a genuine finite Gaussian KL divergence. -/
theorem diagonalGaussianDefect_third_order_expansion :
    Tendsto (fun n : ℕ=>(n:ℝ)^3*(diagonalGaussianDefect n-
      (3/100:ℝ)/(n:ℝ)^2-(9/250:ℝ)/(n:ℝ)^3)) atTop (𝓝 0) := by
  have ht := standardizedDiagonal_gibbs_profile_error_tendsto.add
    uniformEdgeworthEntropyProfile_integral_expansion
  simp only [zero_add] at ht
  apply ht.congr'
  exact Filter.Eventually.of_forall fun n=>by
    dsimp only
    ring

end
end ENT.Quantitative
