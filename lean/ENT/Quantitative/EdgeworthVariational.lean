module

public import ENT.Quantitative.EdgeworthHermite
public import ENT.Small.OcticMoments
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The variational inequality with a quartic Hermite test gives the leading lower bound on the standardized diagonal entropy defect. The proof uses a global one-sided Taylor remainder. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Polynomial
open scoped BigOperators Topology

namespace ENT.Quantitative
noncomputable section

private theorem exp_taylor_two {y : ℝ} (hy : y ≠ 0) :
    ∃ z ∈ uIoo (0:ℝ) y,
      Real.exp y = 1 + y + y^2/2 + Real.exp z * y^3/6 := by
  have hi (k : ℕ) : iteratedDeriv k Real.exp = Real.exp := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  have hd (k : ℕ) : iteratedDerivWithin k Real.exp (uIcc 0 y) 0 = 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hy.symm)
      Real.contDiff_exp.contDiffAt left_mem_uIcc, hi, Real.exp_zero]
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.exp) (n := 2) hy.symm Real.contDiff_exp.contDiffOn
  have hp : taylorWithinEval Real.exp 2 (uIcc 0 y) 0 y = 1 + y + y^2/2 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hd, smul_eq_mul]
    ring
  rw [hp, hi] at he
  norm_num at he
  exact ⟨z, hz, by linarith⟩

theorem exp_neg_hermite4_upper {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    Real.exp (-t * hermite4Even.eval (x^2)) ≤
      1 - t * hermite4Even.eval (x^2) +
        t^2/2 * (hermite4Even.eval (x^2))^2 + 36 * Real.exp 6 * t^3 := by
  let y := -t * hermite4Even.eval (x^2)
  have hy : y ≤ 6*t := by
    dsimp [y]
    nlinarith [mul_le_mul_of_nonneg_left (hermite4Even_lower x) ht]
  have hy6 : y ≤ 6 := hy.trans (by linarith)
  have he : Real.exp y ≤ 1 + y + y^2/2 + 36*Real.exp 6*t^3 := by
    by_cases hy0 : y = 0
    · rw [hy0, Real.exp_zero]
      have hrem : 0 ≤ 36*Real.exp 6*t^3 := by positivity
      nlinarith
    obtain ⟨z, hz, he⟩ := exp_taylor_two hy0
    rw [he]
    have hz6 : z ≤ 6 := by
      have : z < max (0:ℝ) y := hz.2
      exact this.le.trans (max_le (by norm_num) hy6)
    by_cases hynonneg : 0 ≤ y
    · have hcube : y^3 ≤ (6*t)^3 := pow_le_pow_left₀ hynonneg hy 3
      have hb := mul_le_mul (Real.exp_le_exp.mpr hz6) hcube
        (pow_nonneg hynonneg 3) (Real.exp_pos 6).le
      nlinarith
    · have hyneg : y ≤ 0 := le_of_not_ge hynonneg
      have hcube : y^3 ≤ 0 := by nlinarith [sq_nonneg y]
      have hterm := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos z).le hcube
      have hrem : 0 ≤ 36*Real.exp 6*t^3 := by positivity
      linarith
  dsimp [y] at he
  convert he using 1 <;> ring

/-- Unnormalized Gibbs variational inequality, with all integrability
hypotheses explicit. No entropy for the exponential test density is needed. -/
theorem FiniteKLData.test_lower_bound {μ ν : Measure ℝ}
    {p : FiniteEntropyDensity μ} {q : FiniteEntropyDensity ν}
    (h : FiniteKLData p q) (f : ℝ → ℝ)
    (hq : ∀ x, 0 < q.density x)
    (hf : Integrable (fun x => p.density x * f x))
    (hZ : Integrable (fun x => q.density x * Real.exp (f x))) :
    (∫ x, p.density x * f x) + 1 - (∫ x, q.density x * Real.exp (f x)) ≤
      h.klDivergence := by
  have hscalar (x : ℝ) : p.density x * f x + q.density x -
      q.density x * Real.exp (f x) ≤ gibbsDefect (p.density x) (q.density x) := by
    have hg := gibbsDefect_nonneg (p.nonneg x)
      (mul_pos (hq x) (Real.exp_pos (f x))).le
      (fun hz => False.elim ((mul_pos (hq x) (Real.exp_pos (f x))).ne' hz))
    rw [gibbsDefect, Real.log_mul (hq x).ne' (Real.exp_ne_zero _), Real.log_exp] at hg
    unfold gibbsDefect
    nlinarith
  have hmono := integral_mono ((hf.fun_add q.integrable).sub' hZ)
    h.integrable_gibbsDefect hscalar
  rw [integral_sub (hf.fun_add q.integrable) hZ,
    integral_add hf q.integrable, q.mass_one, h.integral_gibbsDefect_eq] at hmono
  exact hmono

theorem standardizedProjection_moment_four {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, x^4 ∂standardizedProjectionLaw a) = 3 - (6/5:ℝ) * ∑ i, (a i)^4 :=
  Small.varianceOne_moment_four a ha

theorem diagonal_sum_fourth {n : ℕ} (hn : 0 < n) :
    (∑ i, (diagonal n i)^4) = (n:ℝ)⁻¹ := by
  have h := deficit_eq_sum_pow_four_sub_inv hn (isUnit_diagonal hn)
  have h0 := (deficit_eq_zero_iff (diagonal n)).mpr (isDiagonal_diagonal n)
  linarith

theorem integrable_hermite4_projection {n : ℕ} (a : Fin n → ℝ) :
    Integrable (fun x => hermite4Even.eval (x^2)) (standardizedProjectionLaw a) := by
  let : IsProbabilityMeasure (standardizedProjectionLaw a) := by
    unfold standardizedProjectionLaw
    infer_instance
  simp_rw [hermite4Even_eval]
  exact ((integrable_standardizedProjection_pow a 4).sub'
    ((integrable_standardizedProjection_pow a 2).const_mul 6)).fun_add (integrable_const 3)

theorem integral_hermite4_diagonal {n : ℕ} (hn : 0 < n) :
    (∫ x, hermite4Even.eval (x^2) ∂standardizedProjectionLaw (diagonal n)) =
      -6 / (5*(n:ℝ)) := by
  let : IsProbabilityMeasure (standardizedProjectionLaw (diagonal n)) := by
    unfold standardizedProjectionLaw
    infer_instance
  simp_rw [hermite4Even_eval]
  rw [integral_add ((integrable_standardizedProjection_pow _ 4).sub'
    ((integrable_standardizedProjection_pow _ 2).const_mul 6)) (integrable_const 3),
    integral_sub (integrable_standardizedProjection_pow _ 4)
      ((integrable_standardizedProjection_pow _ 2).const_mul 6),
    integral_const_mul, integral_const,
    standardizedProjection_moment_four _ (isUnit_diagonal hn),
    integral_standardizedProjection_sq _ (isUnit_diagonal hn), diagonal_sum_fourth hn]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  ring

def quarticGaussianTest (t x : ℝ) : ℝ := -t * hermite4Even.eval (x^2)

theorem integrable_quarticGaussianTest_density {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => gaussianPDFReal 0 1 x * Real.exp (quarticGaussianTest t x)) := by
  apply ((integrable_gaussianPDFReal 0 1).mul_const (Real.exp (6*t))).mono'
  · unfold quarticGaussianTest
    fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (gaussianPDFReal_nonneg 0 1 x) (Real.exp_pos _).le)]
    apply mul_le_mul_of_nonneg_left _ (gaussianPDFReal_nonneg 0 1 x)
    apply Real.exp_le_exp.mpr
    unfold quarticGaussianTest
    nlinarith [mul_le_mul_of_nonneg_left (hermite4Even_lower x) ht]

theorem quarticGaussianTest_integral_upper {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ x, gaussianPDFReal 0 1 x * Real.exp (quarticGaussianTest t x)) ≤
      1 + 12*t^2 + 36*Real.exp 6*t^3 := by
  let p : ℝ[X] := 1 - Polynomial.C t * hermite4Even +
    Polynomial.C (t^2/2) * hermite4Even^2 + Polynomial.C (36*Real.exp 6*t^3)
  have hp (x : ℝ) : p.eval (x^2) = 1 - t * hermite4Even.eval (x^2) +
      t^2/2 * (hermite4Even.eval (x^2))^2 + 36*Real.exp 6*t^3 := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_pow]
  have hmono := integral_mono (integrable_quarticGaussianTest_density ht)
    (integrable_evenPolynomial_gaussian p) (fun x => show
      gaussianPDFReal 0 1 x * Real.exp (quarticGaussianTest t x) ≤
        p.eval (x^2) * gaussianPDFReal 0 1 x by
      rw [hp]
      exact (mul_le_mul_of_nonneg_left (exp_neg_hermite4_upper ht ht1 x)
        (gaussianPDFReal_nonneg 0 1 x)).trans_eq (by ring))
  have hvalue : gaussianEvenPolynomialIntegral p = 1 + 12*t^2 + 36*Real.exp 6*t^3 := by
    have he : p = Polynomial.C 1 - t • hermite4Even +
        (t^2/2) • hermite4Even^2 + Polynomial.C (36*Real.exp 6*t^3) := by
      simp only [p, Polynomial.smul_eq_C_mul, map_one]
    rw [he, map_add, map_add, map_sub, map_smul, map_smul,
      gaussianEvenPolynomialIntegral_C, gaussianEvenPolynomialIntegral_C,
      gaussianIntegral_hermite4, gaussianIntegral_hermite4_sq]
    simp only [smul_eq_mul]
    ring
  exact hmono.trans_eq hvalue

end
end ENT.Quantitative
