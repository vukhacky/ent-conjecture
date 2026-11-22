module

public import ENT.Statement
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! Differential entropy is independent of the chosen density representative. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ENT

noncomputable section

theorem FiniteEntropyDensity.isProbabilityMeasure {μ : Measure ℝ}
    (p : FiniteEntropyDensity μ) : IsProbabilityMeasure μ := by
  refine ⟨?_⟩
  rw [p.law_eq, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal p.integrable
    (Filter.Eventually.of_forall p.nonneg), p.mass_one, ENNReal.ofReal_one]

theorem FiniteEntropyDensity.density_ae_eq {μ : Measure ℝ}
    (p q : FiniteEntropyDensity μ) : p.density =ᵐ[volume] q.density := by
  have h : (fun x => ENNReal.ofReal (p.density x)) =ᵐ[volume]
      (fun x => ENNReal.ofReal (q.density x)) :=
    (withDensity_eq_iff_of_sigmaFinite
      p.measurable.ennreal_ofReal.aemeasurable
      q.measurable.ennreal_ofReal.aemeasurable).mp (p.law_eq.symm.trans q.law_eq)
  filter_upwards [h] with x hx
  have hreal := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (p.nonneg x), ENNReal.toReal_ofReal (q.nonneg x)]
    using hreal

theorem FiniteEntropyDensity.entropy_eq {μ : Measure ℝ}
    (p q : FiniteEntropyDensity μ) : p.entropy = q.entropy := by
  unfold FiniteEntropyDensity.entropy
  congr 1
  apply integral_congr_ae
  filter_upwards [p.density_ae_eq q] with x hx
  rw [hx]

theorem entropyLawInvariance : EntropyLawInvariance := by
  intro μ p q
  exact p.entropy_eq q

/-- Transport an actual finite-entropy density along an equality of laws. -/
def FiniteEntropyDensity.transport {μ ν : Measure ℝ} (p : FiniteEntropyDensity μ)
    (h : μ = ν) : FiniteEntropyDensity ν := h ▸ p

@[simp]
theorem FiniteEntropyDensity.entropy_transport {μ ν : Measure ℝ}
    (p : FiniteEntropyDensity μ) (h : μ = ν) :
    (p.transport h).entropy = p.entropy := by
  subst ν
  rfl

end
end ENT
