module

public import ENT.Small.QuadratureEntropy4
public import ENT.Small.EnclosuresFour

/-! Entropy bounds for the actual diagonal densities, derived from kernel-checked log quadrature. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace ENT.Small
noncomputable section
open Spline Quadrature

theorem diagonal_entropy_formula_half (n : ℕ) (hn : 2 ≤ n) :
    (diagonalFiniteEntropyDensity n hn).entropy =
      -2 * (-((n-1:ℕ):ℝ)/((Nat.factorial (n-1):ℝ)*(n:ℝ)^2) -
        Real.log (Nat.factorial (n-1):ℝ)/((Nat.factorial (n-1):ℝ)*(n:ℝ)) +
        (∫ t in (1:ℝ)..((n:ℝ)/2), unitSumSplineDensity n t * Real.log (unitSumSplineDensity n t))) +
      Real.log 2 - Real.log (n:ℝ)/2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hf : Continuous (fun t : ℝ => unitSumSplineDensity n t * Real.log (unitSumSplineDensity n t)) :=
    Real.continuous_mul_log.comp (continuous_unitSumSplineDensity n)
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hf.intervalIntegrable 0 1) (hf.intervalIntegrable 1 ((n:ℝ)/2))
  rw [diagonal_entropy_eq_unitSum_integral n hn, unitSum_entropy_half n hn,
    ←hs,unitSum_entropy_outer_integral n hn,
    Real.log_div (by norm_num : (2:ℝ)≠0) (Real.sqrt_pos.mpr hn0).ne',Real.log_sqrt hn0.le]
  ring

theorem log_six_eq : Real.log (6:ℝ) = Real.log 2 + Real.log 3 := by
  rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]

theorem fourH_bounds : (86673511/100000000:ℝ) ≤ fourH ∧ fourH ≤ (86673512/100000000:ℝ) := by
  have he := diagonal_entropy_formula_half 4 (by decide)
  norm_num at he
  rw [log_six_eq, show (4:ℝ)=2^2 by norm_num,Real.log_pow] at he
  change fourH = _ at he
  have hm := unitSum_entropy_middle_4_bounds
  norm_num at he
  constructor <;> linarith [hm.1,hm.2,log_two_bounds.1,log_two_bounds.2,log_three_bounds.1,log_three_bounds.2]

theorem varianceOne_diagonal_entropy_four_lower :
    (1416041261/1000000000:ℝ) ≤ (diagonalFiniteEntropyDensity 4 (by decide)).entropy + Real.log (Real.sqrt 3) := by
  have he := diagonal_entropy_formula_half 4 (by decide)
  norm_num at he
  rw [log_six_eq, show (4:ℝ)=2^2 by norm_num,Real.log_pow] at he
  rw [Real.log_sqrt (by norm_num : (0:ℝ)≤3)]
  linarith [unitSum_entropy_middle_4_bounds.2,log_two_bounds.1,log_three_bounds.1]

end
end ENT.Small
