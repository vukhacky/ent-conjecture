module

public import ENT.Statement
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Order.Compact

/-! Bounded, compactly supported densities have finite differential entropy. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory

namespace ENT

noncomputable section

theorem integrable_of_bounded_support {f : ℝ → ℝ} {M R : ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (hM : ∀ x, f x ≤ M)
    (hsupport : ∀ x, x ∉ Set.Icc (-R) R → f x = 0) : Integrable f volume := by
  have hbound : ∀ x, ‖f x‖ ≤ M := by
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 x)] using hM x
  have hint : IntegrableOn f (Set.Icc (-R) R) volume :=
    Measure.integrableOn_of_bounded (by simp [Real.volume_Icc]) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  exact hint.integrable_of_forall_notMem_eq_zero hsupport

theorem integrable_mul_log_of_bounded_support {f : ℝ → ℝ} {M R : ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (hM : ∀ x, f x ≤ M)
    (hsupport : ∀ x, x ∉ Set.Icc (-R) R → f x = 0) :
    Integrable (fun x => f x * Real.log (f x)) volume := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) M)).bddAbove_image
    Real.continuous_mul_log.norm.continuousOn
  have hbound : ∀ x, ‖f x * Real.log (f x)‖ ≤ C := by
    intro x
    exact hC ⟨f x, ⟨h0 x, hM x⟩, rfl⟩
  have hmeas : Measurable (fun x => f x * Real.log (f x)) :=
    Real.continuous_mul_log.measurable.comp hf
  have hint : IntegrableOn (fun x => f x * Real.log (f x)) (Set.Icc (-R) R) volume :=
    Measure.integrableOn_of_bounded (by simp [Real.volume_Icc]) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  apply hint.integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [hsupport x hx, zero_mul]

/-- Construct a genuine finite-entropy density from measurable bounded density data. -/
def finiteEntropyDensityOfBoundedSupport (μ : Measure ℝ) (f : ℝ → ℝ) (M R : ℝ)
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (hM : ∀ x, f x ≤ M)
    (hsupport : ∀ x, x ∉ Set.Icc (-R) R → f x = 0)
    (hmass : (∫ x, f x) = 1)
    (hlaw : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    FiniteEntropyDensity μ where
  density := f
  nonneg := h0
  measurable := hf
  integrable := integrable_of_bounded_support hf h0 hM hsupport
  mass_one := hmass
  law_eq := hlaw
  entropy_integrable := integrable_mul_log_of_bounded_support hf h0 hM hsupport

theorem integral_eq_one_of_density_law {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Integrable f volume) (h0 : ∀ x, 0 ≤ f x)
    (hlaw : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    (∫ x, f x) = 1 := by
  have hmass : ENNReal.ofReal (∫ x, f x) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall h0)]
    calc
      _ = μ Set.univ := by
        rw [hlaw, withDensity_apply _ MeasurableSet.univ]
        simp only [Measure.restrict_univ]
      _ = 1 := measure_univ
  have hreal := congrArg ENNReal.toReal hmass
  simpa only [ENNReal.toReal_ofReal (integral_nonneg h0), ENNReal.toReal_one] using hreal

/-- For a normalized law, the density identity implies that the density integrates to one. -/
def finiteEntropyDensityOfBoundedSupportLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (M R : ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (hM : ∀ x, f x ≤ M) (hsupport : ∀ x, x ∉ Set.Icc (-R) R → f x = 0)
    (hlaw : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    FiniteEntropyDensity μ :=
  finiteEntropyDensityOfBoundedSupport μ f M R hf h0 hM hsupport
    (integral_eq_one_of_density_law (integrable_of_bounded_support hf h0 hM hsupport) h0 hlaw)
    hlaw

end
end ENT
