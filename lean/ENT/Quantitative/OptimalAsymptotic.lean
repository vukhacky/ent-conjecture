module

public import ENT.Quantitative.SharpnessReduction
public import ENT.Quantitative.LargeStability

/-! Lower bound for the asymptotic optimal stability coefficient and its relation to the entropic Edgeworth expansion. -/

@[expose] public section
set_option autoImplicit false
open Filter
open scoped Topology

namespace ENT.Quantitative
noncomputable section

theorem asymptoticKLStability_proved : AsymptoticKLStability := by
  intro η hη
  obtain ⟨N, hN, h⟩ := asymptotic_kl_stability hη
  filter_upwards [eventually_ge_atTop N] with n hn
  exact h n hn

theorem asymptoticEntropyStability_proved : AsymptoticEntropyStability :=
  asymptoticKLStability_proved.entropy

/-- The lower half of the sharp-coefficient limit, with no remaining
analytic hypothesis. -/
theorem eventually_optimalCoefficient_gt {l : ℝ} (hl : l < 3/50) :
    ∀ᶠ n : ℕ in atTop, l < optimalCoefficient n :=
  eventually_optimalCoefficient_gt_of_stability asymptoticEntropyStability_proved hl

/-- Conditional only on the specialized entropic Edgeworth expansion.
The large-dimensional lower bound is supplied by a closed proof term. -/
theorem optimalCoefficient_tendsto_of_uniformEntropicEdgeworth
    (hE : UniformEntropicEdgeworth) :
    Tendsto optimalCoefficient atTop (𝓝 (3/50:ℝ)) :=
  optimalCoefficient_tendsto_of_edgeworth_and_kl_stability hE asymptoticKLStability_proved

end
end ENT.Quantitative
