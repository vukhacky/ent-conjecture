module

public import ENT.Historical.ConditionalVarianceTwo
public import ENT.Historical.CappedVarianceSingular

/-! The manuscript's conditional small-perturbation lemma in all positive
dimensions, including genuine conditional expectation and singular tests. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace ENT.Small
noncomputable section

theorem zero_sum_fin_one (b : Fin 1 → ℝ) (hb : ∑ i, b i = 0) : b = 0 := by
  have hb0 : b 0 = 0 := by simpa using hb
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa [hi] using hb0

theorem conditional_variance_all {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) :
    (cubeLaw n)[(fun x => projection b x^2) | diagonalSigma n] ≤ᵐ[cubeLaw n]
      (fun x => perturbationEnergy b / ((n:ℝ)+1) *
        diagonalDistance n (projection (diagonal n) x)^2) := by
  by_cases hn3 : 3 ≤ n
  · exact conditional_variance_ge_three hn3 b hb
  · have hn12 : n = 1 ∨ n = 2 := by omega
    rcases hn12 with rfl | rfl
    · rw [zero_sum_fin_one b hb]
      simp only [projection, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_pow (by decide : 2 ≠ 0),
        condExp_fun_zero, perturbationEnergy, zero_div]
      exact Filter.Eventually.of_forall (fun _ => le_rfl)
    · convert conditional_variance_two b hb using 1 <;> norm_num

theorem conditional_small_lemma_all {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {γ : ℝ}
    (hγ : ∀ i, Real.sqrt (n:ℝ)*|b i| ≤ γ) :
    (cubeLaw n)[projection b | diagonalSigma n] =ᵐ[cubeLaw n] (fun _ => 0) ∧
    (∀ᵐ x ∂cubeLaw n, |projection b x| ≤ γ*diagonalDistance n (projection (diagonal n) x)) ∧
    (cubeLaw n)[(fun x => projection b x^2) | diagonalSigma n] ≤ᵐ[cubeLaw n]
      (fun x => perturbationEnergy b / ((n:ℝ)+1) *
        diagonalDistance n (projection (diagonal n) x)^2) :=
  ⟨conditional_mean_zero hn b hb, projection_support_distance_ae hn b hb hγ,
    conditional_variance_all hn b hb⟩

theorem integrable_projection_sq_boundary_test {n : ℕ} (hn : 0<n)
    (b : Fin n → ℝ) (hb : ∑ i,b i=0) (f : ℝ → ℝ) (hm : Measurable f)
    (hf0 : ∀ x,0≤f x)
    (hD : Integrable (fun x=>diagonalDistance n (projection (diagonal n) x)^2*
      f (projection (diagonal n) x)) (cubeLaw n)) :
    Integrable (fun x=>projection b x^2*f (projection (diagonal n) x)) (cubeLaw n) := by
  let γ := Real.sqrt ((n:ℝ)-1)*Real.sqrt (perturbationEnergy b)
  have hY : ∀ᵐ x ∂cubeLaw n,projection b x^2≤γ^2*
      diagonalDistance n (projection (diagonal n) x)^2 := by
    filter_upwards [cubeLaw_ae_mem n] with x hx
    have h := projection_zero_sum_support_distance hn b x hb hx
      (fun i=>zero_sum_coordinate_abs_bound b hb i)
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa only [γ,diagonalDistance,sq_abs,mul_pow] using hs
  apply (hD.const_mul (γ^2)).mono_nonneg
    (((measurable_projection b).pow_const 2).mul
      (hm.comp (measurable_projection (diagonal n)))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x=>mul_nonneg (sq_nonneg _) (hf0 _))
  filter_upwards [hY] with x hx
  simpa only [mul_assoc,Pi.mul_apply,Function.comp_apply] using mul_le_mul_of_nonneg_right hx (hf0 _)

theorem integral_variance_bound_nonnegative_test_positive {n : ℕ} (hn : 0<n)
    (b : Fin n → ℝ) (hb : ∑ i,b i=0) (f : ℝ → ℝ) (hm : Measurable f)
    (hf0 : ∀ x,0≤f x)
    (hD : Integrable (fun x=>diagonalDistance n (projection (diagonal n) x)^2*
      f (projection (diagonal n) x)) (cubeLaw n)) :
    Integrable (fun x=>projection b x^2*f (projection (diagonal n) x)) (cubeLaw n) ∧
      (∫ x,projection b x^2*f (projection (diagonal n) x) ∂cubeLaw n)≤
        perturbationEnergy b/((n:ℝ)+1)*
          ∫ x,diagonalDistance n (projection (diagonal n) x)^2*f (projection (diagonal n) x) ∂cubeLaw n := by
  by_cases hn3 : 3 ≤ n
  · exact integral_variance_bound_nonnegative_test_all hn3 b hb f hm hf0 hD
  · refine ⟨integrable_projection_sq_boundary_test hn b hb f hm hf0 hD, ?_⟩
    have hn12 : n = 1 ∨ n = 2 := by omega
    rcases hn12 with rfl | rfl
    · rw [zero_sum_fin_one b hb]
      simp [projection, perturbationEnergy]
    · convert (integral_variance_two b hb f hm).le using 1 <;> norm_num

end
end ENT.Small
