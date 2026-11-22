module

public import ENT.Historical.CappedSimplex
public import ENT.Small.VarianceBound

/-! Dimension-free conditional variance estimate from the actual capped
coordinate marginal.  The pointwise kernel bound holds for every n ≥ 3. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ENT.Small
noncomputable section
open Spline Historical

theorem integral_coordinateWeight_expand (p : ℝ → ℝ)
    (hp : Integrable p volume) (hxp : Integrable (fun x => x * p x) volume)
    (hx2p : Integrable (fun x => x ^ 2 * p x) volume) :
    (∫ x, (1 - 2 * x) ^ 2 * p x) =
      (∫ x, p x) - 4 * (∫ x, x * p x) + 4 * (∫ x, x ^ 2 * p x) := by
  have hfun : (fun x => (1 - 2 * x) ^ 2 * p x) =
      (fun x => p x - 4 * (x * p x) + 4 * (x ^ 2 * p x)) := by
    ext x
    ring
  have hsub : Integrable (fun x => p x - 4 * (x * p x)) volume := by
    convert hp.sub (hxp.const_mul 4) using 1
  rw [hfun, integral_add hsub (hx2p.const_mul 4),
    integral_sub hp (hxp.const_mul 4), integral_const_mul, integral_const_mul]

theorem coordinateSquareKernel_upper_interior (n : ℕ) (hn : 3 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) :
    coordinateSquareKernel n s ≤
      (1 - 4 * s / n + 8 * s ^ 2 / ((n : ℝ) * (n + 1))) * unitSumSplineDensity n s := by
  have hm := cappedMarginal_second_moment_le n hn hs
  have hI := integral_coordinateWeight_expand (cappedMarginalDensity n s)
    (cappedMarginalDensity_integrable n s)
    (cappedMarginalDensity_test_integrable n hn s continuous_id.continuousOn)
    (cappedMarginalDensity_test_integrable n hn s (by fun_prop))
  rw [cappedMarginalDensity_mass n hn hs, cappedMarginalDensity_mean n hn hs,
    cappedMarginalDensity_integral_test] at hI
  change coordinateSquareKernel n s / unitSumSplineDensity n s = _ at hI
  apply (div_le_iff₀ (unitSumSplineDensity_pos n (by omega) s hs.1 hs.2)).mp
  rw [hI]
  convert add_le_add_left (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4))
    (1 - 4 * (s / n)) using 1 <;> ring

theorem varianceKernel_upper_interior (n : ℕ) (hn : 3 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) :
    varianceKernel n s ≤ 4 * s ^ 2 / ((n : ℝ) * (n + 1)) * unitSumSplineDensity n s := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
  have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
  have hK := coordinateSquareKernel_upper_interior n hn hs
  have hle := div_le_div_of_nonneg_right
    (sub_le_sub_right (mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg n))
      (((n : ℝ) - 2 * s) ^ 2 / n * unitSumSplineDensity n s))
    (show 0 ≤ (n : ℝ) - 1 by linarith)
  convert hle using 1
  · rfl
  · field_simp
    ring

theorem varianceKernel_upper_all (n : ℕ) (hn : 3 ≤ n) (s : ℝ) :
    varianceKernel n s ≤ 4 * s ^ 2 / ((n : ℝ) * (n + 1)) * unitSumSplineDensity n s := by
  by_cases hs : s ∈ Icc (0 : ℝ) n
  · have hc : IsClosed {t : ℝ | varianceKernel n t ≤
        4 * t ^ 2 / ((n : ℝ) * (n + 1)) * unitSumSplineDensity n t} :=
      isClosed_le (contDiff_varianceKernel 0 n hn (by omega)).continuous (by
        have := continuous_unitSumSplineDensity n
        fun_prop)
    have hsub : Ioo (0 : ℝ) n ⊆ {t : ℝ | varianceKernel n t ≤
        4 * t ^ 2 / ((n : ℝ) * (n + 1)) * unitSumSplineDensity n t} :=
      fun t ht => varianceKernel_upper_interior n hn ht
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hcl := closure_minimal hsub hc
    rw [closure_Ioo hnpos.ne] at hcl
    exact hcl hs
  · rw [varianceKernel_eq_zero_of_not_mem n hn s hs,
      unitSumSplineDensity_eq_zero_of_not_mem n (by omega) s hs, mul_zero]

theorem varianceKernel_le_distance_density_all (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    varianceKernel n t ≤ diagonalDistance n (sumToDiagonal n t) ^ 2 / ((n : ℝ) + 1) *
      unitSumSplineDensity n t := by
  have hhalf := varianceKernel_upper_all n hn (min t ((n : ℝ) - t))
  have hB : varianceKernel n (min t ((n : ℝ) - t)) = varianceKernel n t := by
    by_cases hh : t ≤ (n : ℝ) - t
    · rw [min_eq_left hh]
    · rw [min_eq_right (le_of_not_ge hh), varianceKernel_reflection n hn]
  have hf : unitSumSplineDensity n (min t ((n : ℝ) - t)) = unitSumSplineDensity n t := by
    by_cases hh : t ≤ (n : ℝ) - t
    · rw [min_eq_left hh]
    · rw [min_eq_right (le_of_not_ge hh), unitSumSplineDensity_reflection n (by omega)]
  rw [hB, hf] at hhalf
  rw [diagonalDistance_sumToDiagonal n (by omega), div_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), div_div]
  convert hhalf using 1 <;> ring

theorem integral_variance_bound_integrable_test_all {n : ℕ} (hn : 3 ≤ n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) (f : ℝ → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable (fun x => f (projection (diagonal n) x)) (cubeLaw n)) :
    (∫ x, projection b x ^ 2 * f (projection (diagonal n) x) ∂cubeLaw n) ≤
      perturbationEnergy b / ((n : ℝ) + 1) *
        ∫ x, diagonalDistance n (projection (diagonal n) x) ^ 2 *
          f (projection (diagonal n) x) ∂cubeLaw n := by
  have hmD : Measurable (fun x => diagonalDistance n x ^ 2 * f x) :=
    ((continuous_diagonalDistance n).measurable.pow_const 2).mul hm
  have hD := integrable_diagonalDistance_sq_test (by omega : 0 < n) hf
  have hDsum := (integrable_diagonal_iff_sum_coordinate n (by omega)
    (fun x => diagonalDistance n x ^ 2 * f x) hmD).mp hD
  have hDint := diagonal_integral_eq_sum_coordinate n (by omega)
    (fun x => diagonalDistance n x ^ 2 * f x) hmD
  have hpoint (t : ℝ) : varianceKernel n t * f (sumToDiagonal n t) ≤
      (unitSumSplineDensity n t * (diagonalDistance n (sumToDiagonal n t) ^ 2 *
        f (sumToDiagonal n t))) / ((n : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_right (varianceKernel_le_distance_density_all n hn t)
      (hf0 (sumToDiagonal n t))
    convert h using 1 <;> ring
  have hle := integral_mono (integrable_varianceKernel_test hn f hm hf)
    (hDsum.div_const ((n : ℝ) + 1)) hpoint
  rw [integral_div] at hle
  rw [integral_zero_sum_projection_sq_eq_varianceKernel hn b hb f hm hf, hDint]
  have h := mul_le_mul_of_nonneg_left hle (perturbationEnergy_nonneg b)
  convert h using 1 <;> ring

end
end ENT.Small
