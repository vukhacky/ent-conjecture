module

public import ENT.Base.One
public import ENT.Base.Two
public import ENT.IIDAE

/-! Closed ENT for n=1,2 on arbitrary probability spaces. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT
noncomputable section
universe u

theorem ent_of_dimension_le_two {n : ℕ} (hn : 1 ≤ n) (hn2 : n ≤ 2) : ENTAt n := by
  interval_cases n
  · exact ent_one
  · exact ent_two

theorem iid_ent_of_dimension_le_two {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (hn : 1 ≤ n) (hn2 : n ≤ 2)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity
      (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) := by
  exact iid_ent_of_entAt μ U hU hind hlaw a ha (ent_of_dimension_le_two hn hn2)

theorem iid_ent_of_dimension_le_two_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (hn : 1 ≤ n) (hn2 : n ≤ 2)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity
      (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) := by
  exact iid_ent_of_entAt_ae μ U hU hind hlaw a ha (ent_of_dimension_le_two hn hn2)

end
end ENT
