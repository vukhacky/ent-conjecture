module

public import ENT.Quantitative.EdgeworthComplete
public import ENT.Quantitative.OptimalAsymptotic

/-! The optimal entropy stability coefficient has the sharp limit 3/50.
The proof uses a closed specialized entropic Edgeworth expansion for the
one-zero direction and a closed asymptotic stability lower bound. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace ENT.Quantitative
noncomputable section

/-- The infimum defining the optimal coefficient is itself admissible.
The zero-deficit case is handled by the proved ENT inequality. -/
theorem entropyStabilityAt_of_le_optimalCoefficient {n : ℕ} (hn : 2 ≤ n) {β : ℝ}
    (hβ : (n:ℝ)*β ≤ optimalCoefficient n) : EntropyStabilityAt n β := by
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
  intro a ha
  let p := projectionFiniteEntropyDensity a ha
  let q := projectionFiniteEntropyDensity (diagonal n) (isUnit_diagonal hn0)
  refine ⟨p, q, ?_⟩
  rw [← projectionEntropy_eq a ha p, ← diagonalEntropy_eq hn0 q]
  rcases eq_or_lt_of_le (deficit_nonneg a) with hδ | hδ
  · rw [← hδ, mul_zero]
    exact sub_nonneg.mpr (projectionEntropy_le_diagonalEntropy hn0 a ha)
  · have hl := hβ.trans (optimalCoefficient_le_slope hn0 a ha hδ)
    unfold normalizedEntropySlope at hl
    have hh := (le_div_iff₀ hδ).mp hl
    have hh' : (n:ℝ)*(β*deficit a) ≤ (n:ℝ)*(diagonalEntropy n-projectionEntropy a ha) := by
      simpa only [mul_assoc] using hh
    exact (mul_le_mul_iff_right₀ hnR).mp hh'

theorem entropyStabilityAt_iff_le_optimalCoefficient {n : ℕ} (hn : 2 ≤ n) (β : ℝ) :
    EntropyStabilityAt n β ↔ (n:ℝ)*β ≤ optimalCoefficient n :=
  ⟨optimalCoefficient_lower_of_stability hn, entropyStabilityAt_of_le_optimalCoefficient hn⟩

theorem optimalCoefficient_is_admissible {n : ℕ} (hn : 2 ≤ n) :
    EntropyStabilityAt n (optimalCoefficient n/(n:ℝ)) := by
  apply entropyStabilityAt_of_le_optimalCoefficient hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  exact le_rfl

/-- The final optimal-coefficient limit has no analytic hypothesis. -/
theorem optimalCoefficient_tendsto :
    Tendsto optimalCoefficient atTop (𝓝 (3/50:ℝ)) :=
  optimalCoefficient_tendsto_of_uniformEntropicEdgeworth uniformEntropicEdgeworth_proved

/-- An explicit admissible sequence attains the limiting upper slope.  The
vector in dimension `n+2` has `n+1` equal nonzero coordinates and one zero. -/
theorem oneZero_normalized_slope_tendsto :
    Tendsto (fun n : ℕ => normalizedEntropySlope (oneZeroCoefficients (n+1))
      (oneZeroCoefficients_isUnit (Nat.succ_pos n))) atTop (𝓝 (3/50:ℝ)) := by
  have h := adjacent_entropy_gap_tendsto.comp (tendsto_add_atTop_nat 1)
  apply h.congr'
  filter_upwards [] with n
  dsimp only [Function.comp_def]
  symm
  simpa only [normalizedEntropySlope, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    oneZeroCoefficients_normalized_gap (Nat.succ_pos n)

/-- No larger fixed asymptotic coefficient can hold in all sufficiently
large dimensions, even without a KL remainder. -/
theorem eventually_no_larger_entropy_stability {c : ℝ} (hc : 3/50 < c) :
    ∀ᶠ n : ℕ in atTop, ¬ EntropyStabilityAt n (c/(n:ℝ)) := by
  have hu := (tendsto_order.mp optimalCoefficient_tendsto).2 c hc
  filter_upwards [hu, eventually_ge_atTop (2:ℕ)] with n hcn hn hs
  have hl := optimalCoefficient_lower_of_stability hn hs
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : (n:ℝ)*(c/(n:ℝ)) = c := by field_simp
  rw [he] at hl
  exact (not_lt_of_ge hl) hcn

end
end ENT.Quantitative
