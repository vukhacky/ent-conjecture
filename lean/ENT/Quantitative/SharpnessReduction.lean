module

public import ENT.Quantitative.AsymptoticDifference
public import ENT.Quantitative.EdgeworthGaussian
public import ENT.Quantitative.OptimalCoefficient

/-! Sharp asymptotic stability from the entropic Edgeworth expansion and the asymptotic lower bound. -/

@[expose] public section
set_option autoImplicit false
open Filter
open scoped Topology

namespace ENT.Quantitative
noncomputable section

/-- The entropic Edgeworth expansion for continuous uniform sums, expressed in terms of their entropy deficit relative to the matching Gaussian. -/
def UniformEntropicEdgeworth : Prop :=
  ∃ c₃ : ℝ, Tendsto (fun n : ℕ => (n : ℝ)^3 *
    (diagonalGaussianDefect n - (3 / 100 : ℝ) / (n : ℝ)^2 - c₃ / (n : ℝ)^3))
      atTop (𝓝 0)

def AsymptoticEntropyStability : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
    EntropyStabilityAt n (((3 / 50 : ℝ) - η) / (n : ℝ))

def AsymptoticKLStability : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
    KLStabilityAt n (((3 / 50 : ℝ) - η) / (n : ℝ))

theorem AsymptoticKLStability.entropy (h : AsymptoticKLStability) :
    AsymptoticEntropyStability := by
  intro η hη
  exact (h η hη).mono fun _ hn => hn.entropyStabilityAt

theorem adjacent_entropy_gap_tendsto_of_edgeworth (h : UniformEntropicEdgeworth) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)^2 * (n : ℝ) *
      (diagonalEntropy (n + 1) - diagonalEntropy n)) atTop (𝓝 (3 / 50 : ℝ)) := by
  obtain ⟨c₃, hc₃⟩ := h
  have ht := scaled_forward_difference_of_order_three diagonalGaussianDefect (3 / 100) c₃ hc₃
  simp only [diagonalGaussianDefect_difference] at ht
  norm_num at ht ⊢
  exact ht

theorem eventually_optimalCoefficient_gt_of_stability
    (h : AsymptoticEntropyStability) {l : ℝ} (hl : l < 3 / 50) :
    ∀ᶠ n : ℕ in atTop, l < optimalCoefficient n := by
  have hη : 0 < ((3 / 50 : ℝ) - l) / 2 := by linarith
  filter_upwards [h _ hη, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hlower := optimalCoefficient_lower_of_stability hn2 hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hc : (n : ℝ) * (((3 / 50 : ℝ) - ((3 / 50 : ℝ) - l) / 2) / (n : ℝ)) =
      (3 / 50 : ℝ) - ((3 / 50 : ℝ) - l) / 2 := by field_simp
  rw [hc] at hlower
  linarith

/-- The exact sharpness implication. Its hypotheses explicitly contain both
the entropy expansion and the asymptotic lower stability estimate. -/
theorem optimalCoefficient_tendsto_of_edgeworth_and_stability
    (hE : UniformEntropicEdgeworth) (hS : AsymptoticEntropyStability) :
    Tendsto optimalCoefficient atTop (𝓝 (3 / 50 : ℝ)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro l hl
    exact (tendsto_add_atTop_nat 1).eventually
      (eventually_optimalCoefficient_gt_of_stability hS hl)
  · intro u hu
    have hupper := (tendsto_order.mp (adjacent_entropy_gap_tendsto_of_edgeworth hE)).2 u hu
    filter_upwards [hupper, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    exact lt_of_le_of_lt (optimalCoefficient_le_adjacent_entropy_gap (by omega)) hn

theorem optimalCoefficient_tendsto_of_edgeworth_and_kl_stability
    (hE : UniformEntropicEdgeworth) (hS : AsymptoticKLStability) :
    Tendsto optimalCoefficient atTop (𝓝 (3 / 50 : ℝ)) :=
  optimalCoefficient_tendsto_of_edgeworth_and_stability hE hS.entropy

end
end ENT.Quantitative
