module

public import ENT.Small.ThreePolynomial
public import ENT.Small.SchurComparison
public import ENT.Small.GibbsPolynomial
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Rational octic approximants, slopes, moment comparisons and finiteness of the associated partition functions. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory

namespace ENT.Small
noncomputable section

def W3 : ℝ → ℝ := octicPolynomial (69 / 200) (81 / 1000) (-113 / 5000) (221 / 100000)
def W4 : ℝ → ℝ := octicPolynomial (4065 / 10000) (301 / 10000) (-563 / 100000) (518 / 1000000)
def W5 : ℝ → ℝ := octicPolynomial (43346 / 100000) (1535 / 100000) (-1769 / 1000000) (17206 / 100000000)
def W6 : ℝ → ℝ := octicPolynomial (44749 / 100000) (1001 / 100000) (-6493 / 10000000) (7284 / 100000000)

theorem W3_moment_comparison (a : Fin 3 → ℝ) (ha : IsUnit a) :
    (1 / 100 : ℝ) * deficit a ≤
      (∫ x, W3 x ∂varianceOneProjectionLaw (diagonal 3)) -
      (∫ x, W3 x ∂varianceOneProjectionLaw a) := three_octic_moment_comparison a ha

theorem W4_moment_comparison (a : Fin 4 → ℝ) (ha : IsUnit a) :
    (11 / 1000 : ℝ) * deficit a ≤
      (∫ x, W4 x ∂varianceOneProjectionLaw (diagonal 4)) -
      (∫ x, W4 x ∂varianceOneProjectionLaw a) := by
  apply small_schur_moment_comparison (by decide) a ha
  all_goals norm_num [octicA, octicB, octicC, octicD]

theorem W5_moment_comparison (a : Fin 5 → ℝ) (ha : IsUnit a) :
    (1 / 100 : ℝ) * deficit a ≤
      (∫ x, W5 x ∂varianceOneProjectionLaw (diagonal 5)) -
      (∫ x, W5 x ∂varianceOneProjectionLaw a) := by
  apply small_schur_moment_comparison (by decide) a ha
  all_goals norm_num [octicA, octicB, octicC, octicD]

theorem W6_moment_comparison (a : Fin 6 → ℝ) (ha : IsUnit a) :
    (19 / 2000 : ℝ) * deficit a ≤
      (∫ x, W6 x ∂varianceOneProjectionLaw (diagonal 6)) -
      (∫ x, W6 x ∂varianceOneProjectionLaw a) := by
  apply small_schur_moment_comparison (by decide) a ha
  all_goals norm_num [octicA, octicB, octicC, octicD]

theorem octicPolynomial_lower_gaussian {c₁ c₂ c₃ c₄ : ℝ}
    (h4 : 0 < c₄) (hdisc : c₃ ^ 2 ≤ 4 * c₂ * c₄) (x : ℝ) :
    c₁ * x ^ 2 ≤ octicPolynomial c₁ c₂ c₃ c₄ x := by
  have hq : 0 ≤ c₂ + c₃ * x ^ 2 + c₄ * x ^ 4 := by
    have hs := sq_nonneg (2 * c₄ * x ^ 2 + c₃)
    have heq : 4 * c₄ * (c₂ + c₃ * x ^ 2 + c₄ * x ^ 4) =
        (2 * c₄ * x ^ 2 + c₃) ^ 2 + (4 * c₂ * c₄ - c₃ ^ 2) := by ring
    have hn : 0 ≤ 4 * c₄ * (c₂ + c₃ * x ^ 2 + c₄ * x ^ 4) := by linarith
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4 * c₄)).mp hn
  have hm := mul_nonneg (pow_nonneg (sq_nonneg x) 2) hq
  unfold octicPolynomial
  nlinarith

theorem octicPolynomial_exp_integrable {c₁ c₂ c₃ c₄ : ℝ}
    (h1 : 0 < c₁) (h4 : 0 < c₄) (hdisc : c₃ ^ 2 ≤ 4 * c₂ * c₄) :
    Integrable (fun x => Real.exp (-octicPolynomial c₁ c₂ c₃ c₄ x)) volume := by
  apply (integrable_exp_neg_mul_sq h1).mono'
    (by unfold octicPolynomial; fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h := octicPolynomial_lower_gaussian (c₁ := c₁) h4 hdisc x
  linarith

theorem W3_exp_integrable : Integrable (fun x => Real.exp (-W3 x)) volume := by
  apply octicPolynomial_exp_integrable <;> norm_num

theorem W4_exp_integrable : Integrable (fun x => Real.exp (-W4 x)) volume := by
  apply octicPolynomial_exp_integrable <;> norm_num

theorem W5_exp_integrable : Integrable (fun x => Real.exp (-W5 x)) volume := by
  apply octicPolynomial_exp_integrable <;> norm_num

theorem W6_exp_integrable : Integrable (fun x => Real.exp (-W6 x)) volume := by
  apply octicPolynomial_exp_integrable <;> norm_num

theorem small_partition_functions_positive :
    0 < partitionFunction W3 ∧ 0 < partitionFunction W4 ∧
      0 < partitionFunction W5 ∧ 0 < partitionFunction W6 :=
  ⟨partitionFunction_pos W3_exp_integrable, partitionFunction_pos W4_exp_integrable,
    partitionFunction_pos W5_exp_integrable, partitionFunction_pos W6_exp_integrable⟩

end
end ENT.Small
