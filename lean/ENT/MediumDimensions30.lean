module

public import ENT.MediumDimensions27
public import ENT.FiniteCertificates.Range28To30
public import ENT.Spline.PureCertificateBridge

/-! Entropy comparison and equality for the stated finite dimension range. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT

theorem ent_of_dimension_seven_through_thirty {n : ℕ}
    (hn0 : 7 ≤ n) (hn1 : n ≤ 30) : ENTAt n := by
  by_cases hn27 : n ≤ 27
  · exact ent_of_dimension_seven_through_twentyseven hn0 hn27
  · exact entAt_of_cellwise_curvature (by omega)
      (Spline.cellwiseCurvature_of_pure_family n (by omega)
        Certificate.PureFast.fastCheckCell Certificate.PureFast.fastCheckCell_sound
        (FiniteCertificates.family_28_30 n (by omega) hn1))

universe u

theorem iid_ent_of_dimension_seven_through_thirty_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn0 : 7 ≤ n) (hn1 : n ≤ 30)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha
    (ent_of_dimension_seven_through_thirty hn0 hn1)

end ENT
