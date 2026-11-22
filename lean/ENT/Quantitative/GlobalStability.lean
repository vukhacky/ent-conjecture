module

public import ENT.Quantitative.LargeStability150

/-! Arbitrary-space asymptotic stability with the dimension threshold chosen
before the probability space, independent uniforms, and coefficient vector. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace ENT.Quantitative
noncomputable section
universe u

theorem iid_asymptotic_kl_stability_ae {η : ℝ} (hη : 0<η) :
    ∃ N : ℕ, 256≤N ∧ ∀ n : ℕ, N≤n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (U : Fin n→Ω→ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
      (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i)=uniformUnit)
      (a : Fin n→ℝ) (ha : IsUnit a),
      ∃ p : FiniteEntropyDensity (μ.map (fun ω=>∑ i,a i*U i ω)),
      ∃ q : FiniteEntropyDensity (μ.map (fun ω=>(Real.sqrt (n:ℝ))⁻¹*∑ i,U i ω)),
      ∃ hKL : FiniteKLData p q,
        ((3/50-η)/(n:ℝ))*deficit a+hKL.klDivergence≤q.entropy-p.entropy := by
  obtain ⟨N,hN,h⟩ := asymptotic_kl_stability hη
  refine ⟨N,hN,?_⟩
  intro n hn Ω _ μ _ U hU hind hlaw a ha
  exact iid_kl_stability_of_ae μ U hU hind hlaw (h n hn) a ha

end
end ENT.Quantitative
