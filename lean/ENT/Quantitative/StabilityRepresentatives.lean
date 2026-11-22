module

public import ENT.Quantitative.StabilityDefinitions

/-! Independence of the quantitative KL statement from the choice of
finite-entropy density representatives of the two probability laws. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory

namespace ENT.Quantitative
noncomputable section

def finiteKLForDensities {μ ν : Measure ℝ}
    {p₀ : FiniteEntropyDensity μ} {q₀ : FiniteEntropyDensity ν}
    (h : FiniteKLData p₀ q₀) (p : FiniteEntropyDensity μ) (q : FiniteEntropyDensity ν) :
    FiniteKLData p q where
  cross_integrable := by
    apply h.cross_integrable.congr
    filter_upwards [p₀.density_ae_eq p, q₀.density_ae_eq q] with x hp hq
    rw [hp, hq]
  support_ae := by
    filter_upwards [h.support_ae, p₀.density_ae_eq p, q₀.density_ae_eq q]
      with x hs hp hq
    rw [← hp, ← hq]
    exact hs

theorem finiteKLForDensities_kl_eq {μ ν : Measure ℝ}
    {p₀ : FiniteEntropyDensity μ} {q₀ : FiniteEntropyDensity ν}
    (h : FiniteKLData p₀ q₀) (p : FiniteEntropyDensity μ) (q : FiniteEntropyDensity ν) :
    (finiteKLForDensities h p q).klDivergence = h.klDivergence := by
  apply integral_congr_ae
  filter_upwards [p₀.density_ae_eq p, q₀.density_ae_eq q] with x hp hq
  rw [hp, hq]

theorem KLStabilityAt.for_densities {n : ℕ} {β : ℝ}
    (h : KLStabilityAt n β) (a : Fin n → ℝ) (ha : IsUnit a)
    (p : FiniteEntropyDensity (projectionLaw a))
    (q : FiniteEntropyDensity (projectionLaw (diagonal n))) :
    ∃ hKL : FiniteKLData p q,
      β * deficit a + hKL.klDivergence ≤ q.entropy - p.entropy := by
  obtain ⟨p₀, q₀, hKL, hgap⟩ := h a ha
  refine ⟨finiteKLForDensities hKL p q, ?_⟩
  rw [finiteKLForDensities_kl_eq]
  rwa [p₀.entropy_eq p, q₀.entropy_eq q] at hgap

end
end ENT.Quantitative
