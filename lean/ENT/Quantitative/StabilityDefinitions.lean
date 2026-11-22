module

public import ENT.Entropy.Gibbs
public import ENT.IIDAE

/-! Quantitative statements retain actual finite-entropy density witnesses.
The KL version also supplies the cross-integrability and support certificate. -/

@[expose] public section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT.Quantitative
noncomputable section

def EntropyStabilityAt (n : ℕ) (β : ℝ) : Prop :=
  ∀ (a : Fin n → ℝ), IsUnit a →
    ∃ p : FiniteEntropyDensity (projectionLaw a),
    ∃ q : FiniteEntropyDensity (projectionLaw (diagonal n)),
      β * deficit a ≤ q.entropy - p.entropy

def KLStabilityAt (n : ℕ) (β : ℝ) : Prop :=
  ∀ (a : Fin n → ℝ), IsUnit a →
    ∃ p : FiniteEntropyDensity (projectionLaw a),
    ∃ q : FiniteEntropyDensity (projectionLaw (diagonal n)),
    ∃ h : FiniteKLData p q,
      β * deficit a + h.klDivergence ≤ q.entropy - p.entropy

theorem KLStabilityAt.entropyStabilityAt {n : ℕ} {β : ℝ}
    (h : KLStabilityAt n β) : EntropyStabilityAt n β := by
  intro a ha
  obtain ⟨p, q, hKL, hgap⟩ := h a ha
  exact ⟨p, q, by linarith [hKL.klDivergence_nonneg]⟩

theorem EntropyStabilityAt.for_densities {n : ℕ} {β : ℝ}
    (h : EntropyStabilityAt n β) (a : Fin n → ℝ) (ha : IsUnit a)
    (p : FiniteEntropyDensity (projectionLaw a))
    (q : FiniteEntropyDensity (projectionLaw (diagonal n))) :
    β * deficit a ≤ q.entropy - p.entropy := by
  obtain ⟨p₀, q₀, hgap⟩ := h a ha
  rwa [p₀.entropy_eq p, q₀.entropy_eq q] at hgap

universe u

theorem iid_entropy_stability_of_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} {β : ℝ}
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (h : EntropyStabilityAt n β) (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      β * deficit a ≤ q.entropy - p.entropy := by
  have hpa := weightedLaw_eq_projectionLaw_ae μ U hU hind hlaw a
  have hdiag : μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω) =
      projectionLaw (diagonal n) := by
    simpa only [diagonal, Finset.mul_sum] using
      weightedLaw_eq_projectionLaw_ae μ U hU hind hlaw (diagonal n)
  rw [hpa, hdiag]
  exact h a ha

theorem iid_kl_stability_of_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} {β : ℝ}
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (h : KLStabilityAt n β) (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
    ∃ hKL : FiniteKLData p q,
      β * deficit a + hKL.klDivergence ≤ q.entropy - p.entropy := by
  have hpa := weightedLaw_eq_projectionLaw_ae μ U hU hind hlaw a
  have hdiag : μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω) =
      projectionLaw (diagonal n) := by
    simpa only [diagonal, Finset.mul_sum] using
      weightedLaw_eq_projectionLaw_ae μ U hU hind hlaw (diagonal n)
  rw [hpa, hdiag]
  exact h a ha

end
end ENT.Quantitative
