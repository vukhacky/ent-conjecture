module

public import ENT.IID

/-! The arbitrary-space interface with almost-everywhere measurability. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT
noncomputable section
universe u

theorem jointLaw_eq_cubeLaw_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit) :
    μ.map (fun ω i => U i ω) = cubeLaw n := by
  rw [iIndepFun.map_fun_eq_pi_map hU hind]
  simp only [hlaw, cubeLaw]

theorem weightedLaw_eq_projectionLaw_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) :
    μ.map (fun ω => ∑ i, a i * U i ω) = projectionLaw a := by
  have hjoint : AEMeasurable (fun ω i => U i ω) μ := AEMeasurable.of_eval hU
  have hmap := AEMeasurable.map_map_of_aemeasurable
    (measurable_projection a).aemeasurable hjoint
  change μ.map (projection a ∘ (fun ω i => U i ω)) = (cubeLaw n).map (projection a)
  rw [← hmap, jointLaw_eq_cubeLaw_ae μ U hU hind hlaw]

theorem iid_ent_of_entAt_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) (hent : ENTAt n) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity
      (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) := by
  obtain ⟨p, q, hle, heq⟩ := hent a ha
  have hpa := weightedLaw_eq_projectionLaw_ae μ U hU hind hlaw a
  have hdiag : μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω) =
      projectionLaw (diagonal n) := by
    simpa only [diagonal, Finset.mul_sum] using
      weightedLaw_eq_projectionLaw_ae μ U hU hind hlaw (diagonal n)
  refine ⟨p.transport hpa.symm, q.transport hdiag.symm, ?_, ?_⟩
  · simpa only [FiniteEntropyDensity.entropy_transport] using hle
  · simpa only [FiniteEntropyDensity.entropy_transport] using heq

end
end ENT
