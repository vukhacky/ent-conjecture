module

public import ENT.Entropy.Gibbs
public import ENT.Comparison.DensityExpectations

/-! Gibbs' variational inequality with all finiteness hypotheses explicit.
This is the analytic interface used by the octic approximants in dimensions
three through six. It does not assume any numerical approximation bound. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory

namespace ENT.Small
noncomputable section

def partitionFunction (W : ℝ → ℝ) : ℝ := ∫ x, Real.exp (-W x)

def normalizedExponential (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-W x) / partitionFunction W

theorem partitionFunction_pos {W : ℝ → ℝ}
    (hW : Integrable (fun x => Real.exp (-W x)) volume) : 0 < partitionFunction W :=
  integral_exp_pos hW

theorem normalizedExponential_pos {W : ℝ → ℝ}
    (hW : Integrable (fun x => Real.exp (-W x)) volume) (x : ℝ) :
    0 < normalizedExponential W x :=
  div_pos (Real.exp_pos _) (partitionFunction_pos hW)

theorem normalizedExponential_integrable {W : ℝ → ℝ}
    (hW : Integrable (fun x => Real.exp (-W x)) volume) :
    Integrable (normalizedExponential W) volume := hW.div_const _

theorem integral_normalizedExponential {W : ℝ → ℝ}
    (hW : Integrable (fun x => Real.exp (-W x)) volume) :
    (∫ x, normalizedExponential W x) = 1 := by
  unfold normalizedExponential
  rw [integral_div]
  exact div_self (partitionFunction_pos hW).ne'

theorem log_normalizedExponential {W : ℝ → ℝ}
    (hW : Integrable (fun x => Real.exp (-W x)) volume) (x : ℝ) :
    Real.log (normalizedExponential W x) = -W x - Real.log (partitionFunction W) := by
  rw [normalizedExponential, Real.log_div (Real.exp_ne_zero _)
    (partitionFunction_pos hW).ne', Real.log_exp]

/-- The real differential entropy is bounded by the genuine partition
function and potential expectation. Integrability is required, so no default
value of an undefined integral can close the conclusion. -/
theorem gibbs_variational_bound {μ : Measure ℝ} (p : FiniteEntropyDensity μ)
    {W : ℝ → ℝ} (hZ : Integrable (fun x => Real.exp (-W x)) volume)
    (hWp : Integrable W μ) :
    p.entropy ≤ Real.log (partitionFunction W) + ∫ x, W x ∂μ := by
  have hpW : Integrable (fun x => p.density x * W x) volume := by
    have h := (p.integrable_iff_density W).mp hWp
    simpa only [mul_comm] using h
  have hpZ : Integrable (fun x => p.density x * Real.log (partitionFunction W)) volume :=
    p.integrable.mul_const _
  have hq := normalizedExponential_integrable hZ
  have hright : Integrable (fun x => p.density x * W x +
      p.density x * Real.log (partitionFunction W) - p.density x +
      normalizedExponential W x) volume :=
    ((hpW.fun_add hpZ).sub' p.integrable).fun_add hq
  have hpoint (x : ℝ) : -(p.density x * Real.log (p.density x)) ≤
      p.density x * W x + p.density x * Real.log (partitionFunction W) -
        p.density x + normalizedExponential W x := by
    have h := ENT.gibbsDefect_nonneg (p.nonneg x) (normalizedExponential_pos hZ x).le
      (fun hz => False.elim ((normalizedExponential_pos hZ x).ne' hz))
    unfold gibbsDefect at h
    rw [log_normalizedExponential hZ] at h
    nlinarith
  have hi := integral_mono_ae p.entropy_integrable.neg hright
    (Filter.Eventually.of_forall hpoint)
  simp only [Pi.neg_apply] at hi
  rw [integral_neg,
    integral_add ((hpW.fun_add hpZ).sub' p.integrable) hq,
    integral_sub (hpW.fun_add hpZ) p.integrable,
    integral_add hpW hpZ, integral_mul_const, p.mass_one,
    integral_normalizedExponential hZ] at hi
  have hWpint : (∫ x, p.density x * W x) = ∫ x, W x ∂μ := by
    rw [p.integral_eq_density W]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm _ _
  rw [hWpint] at hi
  change -(∫ x, p.density x * Real.log (p.density x)) ≤ _
  linarith

def approximationDefect {ν : Measure ℝ} (W : ℝ → ℝ) (q : FiniteEntropyDensity ν) : ℝ :=
  Real.log (partitionFunction W) + (∫ x, W x ∂ν) - q.entropy

theorem approximationDefect_nonneg {ν : Measure ℝ} (q : FiniteEntropyDensity ν)
    {W : ℝ → ℝ} (hZ : Integrable (fun x => Real.exp (-W x)) volume)
    (hWq : Integrable W ν) : 0 ≤ approximationDefect W q :=
  sub_nonneg.mpr (gibbs_variational_bound q hZ hWq)

theorem entropy_gap_ge_potential_gap_sub_approximation {μ ν : Measure ℝ}
    (p : FiniteEntropyDensity μ) (q : FiniteEntropyDensity ν) {W : ℝ → ℝ}
    (hZ : Integrable (fun x => Real.exp (-W x)) volume)
    (hWp : Integrable W μ) (hWq : Integrable W ν) :
    (∫ x, W x ∂ν) - (∫ x, W x ∂μ) - approximationDefect W q ≤ q.entropy - p.entropy := by
  have h := gibbs_variational_bound p hZ hWp
  have hs := approximationDefect_nonneg q hZ hWq
  unfold approximationDefect
  linarith

end
end ENT.Small
