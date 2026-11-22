module

public import ENT.Historical.ConditionalExpectation
public import ENT.Small.VarianceBound

/-! Conditional variance bounds in dimensions five and six from weighted integral inequalities and the order characterization of conditional expectation. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ENT.Small
noncomputable section

theorem integrable_cube_diagonalDistance_sq (n : ℕ) :
    Integrable (fun x => diagonalDistance n (projection (diagonal n) x)^2) (cubeLaw n) := by
  apply Integrable.of_bound
    (((continuous_diagonalDistance n).measurable.comp (measurable_projection (diagonal n))).pow_const 2).aestronglyMeasurable
    ((Real.sqrt (n:ℝ) + projectionRadius (diagonal n))^2)
  filter_upwards [cubeLaw_ae_mem n] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  apply pow_le_pow_left₀ (abs_nonneg _) _ 2
  unfold diagonalDistance
  calc
    abs (Real.sqrt (n:ℝ) - |projection (diagonal n) x|) ≤
        |Real.sqrt (n:ℝ)| + abs (abs (projection (diagonal n) x)) := abs_sub _ _
    _ = Real.sqrt (n:ℝ) + |projection (diagonal n) x| := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_abs]
    _ ≤ _ := add_le_add le_rfl (abs_projection_le_radius (diagonal n) x hx)

theorem integral_mul_diagonal_indicator {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (t : Set ℝ) (ht : MeasurableSet t) :
    (∫ x, F x * t.indicator (fun _ : ℝ => (1:ℝ)) (projection (diagonal n) x) ∂cubeLaw n) =
      ∫ x in (projection (diagonal n)) ⁻¹' t, F x ∂cubeLaw n := by
  rw [← integral_indicator (ht.preimage (measurable_projection (diagonal n)))]
  congr 1
  funext x
  by_cases hx : projection (diagonal n) x ∈ t <;> simp [hx]

theorem integrable_diagonal_indicator (n : ℕ) (t : Set ℝ) (ht : MeasurableSet t) :
    Integrable (fun x => t.indicator (fun _ : ℝ => (1:ℝ))
      (projection (diagonal n) x)) (cubeLaw n) := by
  convert (integrable_const (μ := cubeLaw n) (1:ℝ)).indicator
    (ht.preimage (measurable_projection (diagonal n))) using 1
  rfl

theorem conditional_variance_five_six {n : ℕ} (hn : n=5 ∨ n=6)
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
  have h := integral_variance_bound_integrable_test hn b hb
    (t.indicator (fun _ : ℝ => (1:ℝ))) (measurable_const.indicator ht)
    (fun x => by by_cases hx : x ∈ t <;> simp [hx])
    (integrable_diagonal_indicator n t ht)
  rw [integral_mul_diagonal_indicator _ t ht,
    integral_mul_diagonal_indicator _ t ht] at h
  rw [integral_const_mul]
  exact h

theorem conditional_small_lemma_five_six {n : ℕ} (hn : n=5 ∨ n=6)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {γ : ℝ}
    (hγ : ∀ i, Real.sqrt (n:ℝ)*|b i| ≤ γ) :
    (cubeLaw n)[projection b | diagonalSigma n] =ᵐ[cubeLaw n] (fun _ => 0) ∧
    (∀ᵐ x ∂cubeLaw n, |projection b x| ≤ γ*diagonalDistance n (projection (diagonal n) x)) ∧
    (cubeLaw n)[(fun x => projection b x^2) | diagonalSigma n] ≤ᵐ[cubeLaw n]
      (fun x => perturbationEnergy b / ((n:ℝ)+1) *
        diagonalDistance n (projection (diagonal n) x)^2) :=
  ⟨conditional_mean_zero (by omega) b hb, projection_support_distance_ae (by omega) b hb hγ,
    conditional_variance_five_six hn b hb⟩

end
end ENT.Small
