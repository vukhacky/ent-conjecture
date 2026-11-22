module

public import ENT.Comparison.CurvatureToENT
public import ENT.Pilot.FiniteRange7To20
public import ENT.Pilot.FiniteRange21To23
public import ENT.IIDAE

/-! Finite-dimensional entropy comparison from complete cell coverage. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT

theorem ent_eight : ENTAt 8 :=
  entAt_of_cellwise_curvature (by decide) Pilot.dimension8_cellwise_from_complete_checker

theorem ent_of_dimension_seven_through_seventeen {n : ℕ}
    (hn0 : 7 ≤ n) (hn1 : n ≤ 17) : ENTAt n :=
  entAt_of_cellwise_curvature (by omega)
    (Pilot.cellwise_curvature_seven_through_seventeen n hn0 hn1)

theorem ent_of_dimension_seven_through_twenty {n : ℕ}
    (hn0 : 7 ≤ n) (hn1 : n ≤ 20) : ENTAt n :=
  entAt_of_cellwise_curvature (by omega)
    (Pilot.cellwise_curvature_seven_through_twenty n hn0 hn1)

theorem ent_of_dimension_seven_through_twentythree {n : ℕ}
    (hn0 : 7 ≤ n) (hn1 : n ≤ 23) : ENTAt n := by
  by_cases hn20 : n ≤ 20
  · exact ent_of_dimension_seven_through_twenty hn0 hn20
  · exact entAt_of_cellwise_curvature (by omega)
      (Pilot.cellwise_curvature_twentyone_through_twentythree n (by omega) hn1)

universe u

theorem iid_ent_of_dimension_seven_through_seventeen_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn0 : 7 ≤ n) (hn1 : n ≤ 17)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha (ent_of_dimension_seven_through_seventeen hn0 hn1)

theorem iid_ent_of_dimension_seven_through_twenty_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn0 : 7 ≤ n) (hn1 : n ≤ 20)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha (ent_of_dimension_seven_through_twenty hn0 hn1)

theorem iid_ent_of_dimension_seven_through_twentythree_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn0 : 7 ≤ n) (hn1 : n ≤ 23)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha (ent_of_dimension_seven_through_twentythree hn0 hn1)

end ENT
