module

public import ENT.Historical.CappedVariance

/-! The dimension-free capped-simplex variance bound for singular nonnegative
measurable tests. Integrability is assumed only after multiplication by the
square of the distance to the support boundary. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ENT.Small
noncomputable section
open Spline

theorem integral_variance_bound_nonnegative_test_all {n : ℕ} (hn : 3≤n)
    (b : Fin n → ℝ) (hb : ∑ i,b i=0) (f : ℝ → ℝ) (hm : Measurable f)
    (hf0 : ∀ x,0≤f x)
    (hD : Integrable (fun x=>diagonalDistance n (projection (diagonal n) x)^2*
      f (projection (diagonal n) x)) (cubeLaw n)) :
    Integrable (fun x=>projection b x^2*f (projection (diagonal n) x)) (cubeLaw n) ∧
      (∫ x,projection b x^2*f (projection (diagonal n) x) ∂cubeLaw n)≤
        perturbationEnergy b/((n:ℝ)+1)*
          ∫ x,diagonalDistance n (projection (diagonal n) x)^2*f (projection (diagonal n) x) ∂cubeLaw n := by
  let γ := Real.sqrt ((n:ℝ)-1)*Real.sqrt (perturbationEnergy b)
  let T := projection (diagonal n)
  let Y := projection b
  let D := fun x=>diagonalDistance n (T x)
  have hY : ∀ᵐ x ∂cubeLaw n,Y x^2≤γ^2*D x^2 := by
    filter_upwards [cubeLaw_ae_mem n] with x hx
    have h := projection_zero_sum_support_distance (by omega : 0<n) b x hb hx
      (fun i=>zero_sum_coordinate_abs_bound b hb i)
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa only [γ,Y,D,T,diagonalDistance,sq_abs,mul_pow] using hs
  have hmeasY : Measurable (fun x=>Y x^2*f (T x)) :=
    ((measurable_projection b).pow_const 2).mul (hm.comp (measurable_projection (diagonal n)))
  have hiY : Integrable (fun x=>Y x^2*f (T x)) (cubeLaw n) := by
    apply (hD.const_mul (γ^2)).mono_nonneg hmeasY.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x=>mul_nonneg (sq_nonneg _) (hf0 _))
    filter_upwards [hY] with x hx
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hx (hf0 (T x))
  let fN := fun N : ℕ=>fun t : ℝ=>min (f t) (N:ℝ)
  have hmN (N : ℕ) : Measurable (fN N) := hm.min measurable_const
  have h0N (N : ℕ) (t : ℝ) : 0≤fN N t := le_min (hf0 t) (Nat.cast_nonneg N)
  have hiN (N : ℕ) : Integrable (fun x=>fN N (T x)) (cubeLaw n) := by
    apply (integrable_const (N:ℝ)).mono_nonneg ((hmN N).comp (measurable_projection (diagonal n))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x=>h0N N (T x))
    exact Filter.Eventually.of_forall fun x=>min_le_right _ _
  have hleN (N : ℕ) := integral_variance_bound_integrable_test_all hn b hb (fN N) (hmN N) (h0N N) (hiN N)
  have hlimY : Tendsto (fun N=>∫ x,Y x^2*fN N (T x) ∂cubeLaw n) atTop
      (𝓝 (∫ x,Y x^2*f (T x) ∂cubeLaw n)) := by
    apply tendsto_integral_of_dominated_convergence (fun x=>Y x^2*f (T x))
      (fun N=>(((measurable_projection b).pow_const 2).mul
        ((hmN N).comp (measurable_projection (diagonal n)))).aestronglyMeasurable) hiY
    · intro N
      exact Filter.Eventually.of_forall fun x=>by
        simp only [Pi.mul_apply,Function.comp_apply]
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (h0N N _))]
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
    · exact Filter.Eventually.of_forall fun x=>tendsto_const_nhds.mul (tendsto_min_natCast (f (T x)))
  have hlimD : Tendsto (fun N=>∫ x,D x^2*fN N (T x) ∂cubeLaw n) atTop
      (𝓝 (∫ x,D x^2*f (T x) ∂cubeLaw n)) := by
    apply tendsto_integral_of_dominated_convergence (fun x=>D x^2*f (T x))
      (fun N=>((((continuous_diagonalDistance n).measurable.comp (measurable_projection (diagonal n))).pow_const 2).mul
        ((hmN N).comp (measurable_projection (diagonal n)))).aestronglyMeasurable) hD
    · intro N
      exact Filter.Eventually.of_forall fun x=>by
        simp only [Pi.mul_apply,Function.comp_apply]
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (h0N N _))]
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
    · exact Filter.Eventually.of_forall fun x=>tendsto_const_nhds.mul (tendsto_min_natCast (f (T x)))
  exact ⟨hiY,le_of_tendsto_of_tendsto hlimY (tendsto_const_nhds.mul hlimD)
    (Filter.Eventually.of_forall hleN)⟩

end
end ENT.Small
