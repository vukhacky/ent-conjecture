module

public import ENT.MediumDimensions
public import ENT.Pilot.FiniteRange24To27

/-! Entropy comparison and equality for the stated finite dimension range. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT

theorem ent_of_dimension_seven_through_twentyseven {n : ℕ}
    (hn0 : 7 ≤ n) (hn1 : n ≤ 27) : ENTAt n := by
  by_cases hn23 : n ≤ 23
  · exact ent_of_dimension_seven_through_twentythree hn0 hn23
  · exact entAt_of_cellwise_curvature (by omega)
      (Pilot.FiniteRange24To27_cellwise n (by omega) hn1)

universe u

theorem iid_ent_of_dimension_seven_through_twentyseven_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn0 : 7 ≤ n) (hn1 : n ≤ 27)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha
    (ent_of_dimension_seven_through_twentyseven hn0 hn1)

end ENT
