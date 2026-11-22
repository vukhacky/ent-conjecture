module

public import ENT.Historical.ConditionalVariance
public import ENT.Historical.CappedVariance

/-! The all-dimensional conditional variance conclusion from the capped
coordinate marginal and its proved convex-order comparison. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ENT.Small
noncomputable section

theorem conditional_variance_ge_three {n : ℕ} (hn : 3 ≤ n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) :
    (cubeLaw n)[(fun x => projection b x^2) | diagonalSigma n] ≤ᵐ[cubeLaw n]
      (fun x => perturbationEnergy b / ((n:ℝ)+1) *
        diagonalDistance n (projection (diagonal n) x)^2) := by
  have hT : @Measurable (Fin n → ℝ) ℝ (diagonalSigma n) inferInstance
      (projection (diagonal n)) := Measurable.of_comap_le le_rfl
  apply ENT.Historical.condExp_le_of_setIntegral_le (diagonalSigma_le n)
    (integrable_cube_projection_sq b)
    ((integrable_cube_diagonalDistance_sq n).const_mul _)
    ((((continuous_diagonalDistance n).measurable.comp hT).pow_const 2).const_mul _).stronglyMeasurable
  intro s hs hfin
  obtain ⟨t, ht, rfl⟩ := hs
  have h := integral_variance_bound_integrable_test_all hn b hb
    (t.indicator (fun _ : ℝ => (1:ℝ))) (measurable_const.indicator ht)
    (fun x => by by_cases hx : x ∈ t <;> simp [hx])
    (integrable_diagonal_indicator n t ht)
  rw [integral_mul_diagonal_indicator _ t ht,
    integral_mul_diagonal_indicator _ t ht] at h
  rw [integral_const_mul]
  exact h

theorem conditional_small_lemma_ge_three {n : ℕ} (hn : 3 ≤ n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {γ : ℝ}
    (hγ : ∀ i, Real.sqrt (n:ℝ)*|b i| ≤ γ) :
    (cubeLaw n)[projection b | diagonalSigma n] =ᵐ[cubeLaw n] (fun _ => 0) ∧
    (∀ᵐ x ∂cubeLaw n, |projection b x| ≤ γ*diagonalDistance n (projection (diagonal n) x)) ∧
    (cubeLaw n)[(fun x => projection b x^2) | diagonalSigma n] ≤ᵐ[cubeLaw n]
      (fun x => perturbationEnergy b / ((n:ℝ)+1) *
        diagonalDistance n (projection (diagonal n) x)^2) :=
  ⟨conditional_mean_zero (by omega) b hb, projection_support_distance_ae (by omega) b hb hγ,
    conditional_variance_ge_three hn b hb⟩

end
end ENT.Small
