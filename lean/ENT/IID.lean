module

public import ENT.Basic.Uniform
public import ENT.Entropy.LawInvariance
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-! Transfer of the entropy comparison in a fixed dimension from the canonical product law to independent uniform random variables on an arbitrary probability space. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT

noncomputable section
universe u

theorem jointLaw_eq_cubeLaw {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (U : Fin n → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit) :
    μ.map (fun ω i => U i ω) = cubeLaw n := by
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (hU i).aemeasurable) hind]
  simp only [hlaw, cubeLaw]

theorem weightedLaw_eq_projectionLaw {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (U : Fin n → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) :
    μ.map (fun ω => ∑ i, a i * U i ω) = projectionLaw a := by
  have hjoint : Measurable (fun ω i => U i ω) := Measurable.of_eval hU
  have hmap := Measure.map_map (μ := μ) (measurable_projection a) hjoint
  change μ.map (projection a ∘ (fun ω i => U i ω)) = (cubeLaw n).map (projection a)
  rw [← hmap, jointLaw_eq_cubeLaw μ U hU hind hlaw]

/-- Canonical ENT implies the full independent-variable statement, including
existence of both finite-entropy densities and the exact equality case. -/
theorem iid_ent_of_entAt {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (U : Fin n → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) (hent : ENTAt n) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity
      (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) := by
  obtain ⟨p, q, hle, heq⟩ := hent a ha
  have hpa := weightedLaw_eq_projectionLaw μ U hU hind hlaw a
  have hdiag : μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω) =
      projectionLaw (diagonal n) := by
    simpa only [diagonal, Finset.mul_sum] using
      weightedLaw_eq_projectionLaw μ U hU hind hlaw (diagonal n)
  refine ⟨p.transport hpa.symm, q.transport hdiag.symm, ?_, ?_⟩
  · simpa only [FiniteEntropyDensity.entropy_transport] using hle
  · simpa only [FiniteEntropyDensity.entropy_transport] using heq

end
end ENT
