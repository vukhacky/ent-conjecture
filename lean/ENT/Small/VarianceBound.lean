module

public import ENT.Small.FiveSixAnalysis
public import ENT.Comparison.SupportRadius
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Weighted conditional-variance inequality in dimensions five and six.
Truncation admits singular nonnegative tests using only integrability of
the distance-squared weighted test, as required by the Taylor remainder. -/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ENT.Small
noncomputable section
open Spline

def diagonalDistance (n : ℕ) (x : ℝ) : ℝ := Real.sqrt (n:ℝ)-|x|

theorem continuous_diagonalDistance (n : ℕ) : Continuous (diagonalDistance n) :=
  continuous_const.sub continuous_abs

theorem diagonalDistance_sumToDiagonal (n : ℕ) (hn : 0<n) (t : ℝ) :
    diagonalDistance n (sumToDiagonal n t)=2*min t ((n:ℝ)-t)/Real.sqrt n := by
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n)
  by_cases ht : t≤(n:ℝ)/2
  · have hg : 0≤sumToDiagonal n t := div_nonneg (by linarith) hs.le
    rw [diagonalDistance,abs_of_nonneg hg,min_eq_left (by linarith)]
    unfold sumToDiagonal
    field_simp
    nlinarith only [hs2]
  · have hg : sumToDiagonal n t≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le
    rw [diagonalDistance,abs_of_nonpos hg,min_eq_right (by linarith)]
    unfold sumToDiagonal
    field_simp
    nlinarith only [hs2]

theorem varianceKernel_le_distance_density (n : ℕ) (hn : n=5 ∨ n=6) (t : ℝ) :
    varianceKernel n t≤diagonalDistance n (sumToDiagonal n t)^2/((n:ℝ)+1)*unitSumSplineDensity n t := by
  have hn3 : 3≤n := by omega
  by_cases ht : t∈Icc (0:ℝ) n
  · have hs0 : 0≤min t ((n:ℝ)-t) := le_min ht.1 (by linarith [ht.2])
    have hs1 : min t ((n:ℝ)-t)≤(n:ℝ)/2 := by
      by_cases hh : t≤(n:ℝ)/2
      · exact (min_le_left _ _).trans hh
      · exact (min_le_right _ _).trans (by linarith)
    have hhalf : varianceKernel n (min t ((n:ℝ)-t))≤
        4*(min t ((n:ℝ)-t))^2/((n:ℝ)*((n:ℝ)+1))*unitSumSplineDensity n (min t ((n:ℝ)-t)) := by
      rcases hn with rfl | rfl
      · have h := varianceKernel_five_upper _ hs0 hs1
        norm_num at h ⊢
        exact h
      · have h := varianceKernel_six_upper _ hs0 (by convert hs1 using 1 <;> norm_num)
        norm_num at h ⊢
        exact h
    have hB : varianceKernel n (min t ((n:ℝ)-t))=varianceKernel n t := by
      by_cases hh : t≤(n:ℝ)-t
      · rw [min_eq_left hh]
      · rw [min_eq_right (le_of_not_ge hh),varianceKernel_reflection n hn3]
    have hf : unitSumSplineDensity n (min t ((n:ℝ)-t))=unitSumSplineDensity n t := by
      by_cases hh : t≤(n:ℝ)-t
      · rw [min_eq_left hh]
      · rw [min_eq_right (le_of_not_ge hh),unitSumSplineDensity_reflection n (by omega)]
    rw [hB,hf] at hhalf
    rw [diagonalDistance_sumToDiagonal n (by omega),div_pow,Real.sq_sqrt (Nat.cast_nonneg n),div_div]
    convert hhalf using 1 <;> ring
  · rw [varianceKernel_eq_zero_of_not_mem n hn3 t ht,
      unitSumSplineDensity_eq_zero_of_not_mem n (by omega) t ht,mul_zero]

theorem integrable_diagonalDistance_sq_test {n : ℕ} (hn : 0<n) {f : ℝ → ℝ}
    (hf : Integrable (fun x=>f (projection (diagonal n) x)) (cubeLaw n)) :
    Integrable (fun x=>diagonalDistance n (projection (diagonal n) x)^2*
      f (projection (diagonal n) x)) (cubeLaw n) := by
  apply hf.bdd_mul (c := (n:ℝ)) (((continuous_diagonalDistance n).measurable.comp
    (measurable_projection (diagonal n))).pow_const 2).aestronglyMeasurable
  filter_upwards [cubeLaw_ae_mem n] with x hx
  have hT := (abs_projection_le_radius (diagonal n) x hx).trans
    (projectionRadius_le_sqrt (diagonal n) (isUnit_diagonal hn))
  have hd0 : 0≤diagonalDistance n (projection (diagonal n) x) := sub_nonneg.mpr hT
  have hd : diagonalDistance n (projection (diagonal n) x)≤Real.sqrt n := by
    unfold diagonalDistance
    linarith [abs_nonneg (projection (diagonal n) x)]
  change |diagonalDistance n (projection (diagonal n) x)^2|≤(n:ℝ)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (pow_le_pow_left₀ hd0 hd 2).trans_eq (Real.sq_sqrt (Nat.cast_nonneg n))

theorem varianceKernel_test_eq (n : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    varianceKernel n t*f (sumToDiagonal n t)=
      ((n:ℝ)*(coordinateSquareKernel n t*f (sumToDiagonal n t))-
        unitSumSplineDensity n t*(sumToDiagonal n t^2*f (sumToDiagonal n t)))/((n:ℝ)-1) := by
  simp only [varianceKernel,sumToDiagonal,div_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem integrable_varianceKernel_test {n : ℕ} (hn : 3≤n) (f : ℝ → ℝ)
    (hm : Measurable f) (hf : Integrable (fun x=>f (projection (diagonal n) x)) (cubeLaw n)) :
    Integrable (fun t=>varianceKernel n t*f (sumToDiagonal n t)) volume := by
  have hfn := (integrable_diagonal_iff_sum_coordinate n (by omega) f hm).mp hf
  have hK := integrable_coordinateKernel_test n hn f hm hfn
  have hm2 : Measurable (fun x : ℝ=>x^2*f x) := (measurable_id.pow_const 2).mul hm
  have hf2 := (integrable_diagonal_iff_sum_coordinate n (by omega) (fun x : ℝ=>x^2*f x) hm2).mp
    (integrable_projection_sq_diagonal_test (diagonal n) hf)
  apply (((hK.const_mul (n:ℝ)).sub hf2).div_const ((n:ℝ)-1)).congr
  exact Filter.Eventually.of_forall fun t=>(varianceKernel_test_eq n f t).symm

theorem integral_variance_bound_integrable_test {n : ℕ} (hn : n=5 ∨ n=6)
    (b : Fin n → ℝ) (hb : ∑ i,b i=0) (f : ℝ → ℝ) (hm : Measurable f)
    (hf0 : ∀ x,0≤f x) (hf : Integrable (fun x=>f (projection (diagonal n) x)) (cubeLaw n)) :
    (∫ x,projection b x^2*f (projection (diagonal n) x) ∂cubeLaw n)≤
      perturbationEnergy b/((n:ℝ)+1)*
        ∫ x,diagonalDistance n (projection (diagonal n) x)^2*f (projection (diagonal n) x) ∂cubeLaw n := by
  have hn3 : 3≤n := by omega
  have hmD : Measurable (fun x=>diagonalDistance n x^2*f x) :=
    ((continuous_diagonalDistance n).measurable.pow_const 2).mul hm
  have hD := integrable_diagonalDistance_sq_test (by omega : 0<n) hf
  have hDsum := (integrable_diagonal_iff_sum_coordinate n (by omega)
    (fun x=>diagonalDistance n x^2*f x) hmD).mp hD
  have hDint := diagonal_integral_eq_sum_coordinate n (by omega)
    (fun x=>diagonalDistance n x^2*f x) hmD
  have hpoint (t : ℝ) : varianceKernel n t*f (sumToDiagonal n t)≤
      (unitSumSplineDensity n t*(diagonalDistance n (sumToDiagonal n t)^2*f (sumToDiagonal n t)))/((n:ℝ)+1) := by
    have h := mul_le_mul_of_nonneg_right (varianceKernel_le_distance_density n hn t) (hf0 (sumToDiagonal n t))
    convert h using 1 <;> ring
  have hle := integral_mono (integrable_varianceKernel_test hn3 f hm hf)
    (hDsum.div_const ((n:ℝ)+1)) hpoint
  rw [integral_div] at hle
  rw [integral_zero_sum_projection_sq_eq_varianceKernel hn3 b hb f hm hf,hDint]
  have h := mul_le_mul_of_nonneg_left hle (perturbationEnergy_nonneg b)
  convert h using 1 <;> ring

theorem tendsto_min_natCast (y : ℝ) : Tendsto (fun N : ℕ=>min y (N:ℝ)) atTop (𝓝 y) := by
  obtain ⟨N,hN⟩ := exists_nat_gt y
  have heq : (fun M : ℕ=>min y (M:ℝ))=ᶠ[atTop](fun _=>y) := by
    filter_upwards [eventually_ge_atTop N] with M hM
    exact min_eq_left (hN.le.trans (Nat.cast_le.mpr hM))
  exact tendsto_const_nhds.congr' heq.symm

theorem integral_variance_bound_nonnegative_test {n : ℕ} (hn : n=5 ∨ n=6)
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
  have hleN (N : ℕ) := integral_variance_bound_integrable_test hn b hb (fN N) (hmN N) (h0N N) (hiN N)
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
