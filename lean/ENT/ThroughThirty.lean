module

public import ENT.SmallDimensions
public import ENT.DimensionThree
public import ENT.DimensionFour
public import ENT.DimensionFive
public import ENT.DimensionSix
public import ENT.MediumDimensions30

/-! Exact complete finite prefix, including finite entropy and equality. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT

theorem ent_of_dimension_le_six {n : ℕ} (hn0 : 0 < n) (hn1 : n ≤ 6) : ENTAt n := by
  interval_cases n
  · exact ent_one
  · exact ent_two
  · exact ent_three
  · exact ent_four
  · exact ent_five
  · exact ent_six

theorem ent_of_dimension_le_thirty {n : ℕ} (hn0 : 0 < n) (hn1 : n ≤ 30) : ENTAt n := by
  by_cases h6 : n ≤ 6
  · exact ent_of_dimension_le_six hn0 h6
  · exact ent_of_dimension_seven_through_thirty (by omega) hn1

universe u

theorem iid_ent_of_dimension_le_thirty_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn0 : 0 < n) (hn1 : n ≤ 30)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha (ent_of_dimension_le_thirty hn0 hn1)

end ENT
