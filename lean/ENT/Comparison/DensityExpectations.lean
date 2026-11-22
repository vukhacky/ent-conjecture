module

public import ENT.Comparison.Expectations
public import ENT.Base.TwoDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Integration against a finite-entropy density and against the canonical
projection law. Integrability is transported explicitly when it is used. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory

namespace ENT
noncomputable section

theorem FiniteEntropyDensity.integral_eq_density {μ : Measure ℝ}
    (p : FiniteEntropyDensity μ) (g : ℝ → ℝ) :
    (∫ x, g x ∂μ) = ∫ x, g x * p.density x := by
  conv_lhs => rw [p.law_eq]
  rw [integral_withDensity_eq_integral_toReal_smul
    p.measurable.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (p.nonneg _), smul_eq_mul, mul_comm]

theorem FiniteEntropyDensity.integrable_iff_density {μ : Measure ℝ}
    (p : FiniteEntropyDensity μ) (g : ℝ → ℝ) :
    Integrable g μ ↔ Integrable (fun x => g x * p.density x) volume := by
  conv_lhs => rw [p.law_eq]
  rw [integrable_withDensity_iff p.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (p.nonneg _)]

namespace Comparison

theorem potentialExpectation_eq_integral_law {n : ℕ} (a : Fin n → ℝ)
    {g : ℝ → ℝ} (hg : Continuous g) :
    potentialExpectation g a = ∫ x, g x ∂projectionLaw a := by
  symm
  exact integral_map (measurable_projection a).aemeasurable hg.aestronglyMeasurable

theorem potentialExpectation_twoDensity {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℝ → ℝ} (hg : Continuous g) :
    potentialExpectation g ![a, b] = ∫ x, g x * twoDensity a b x := by
  rw [potentialExpectation_eq_integral_law _ hg]
  exact (twoFiniteEntropyDensity ![a, b] ha hb).integral_eq_density g

end Comparison
end
end ENT
