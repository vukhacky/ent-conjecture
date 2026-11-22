module

public import ENT.FiniteCertificates.CurvatureThrough30
public import ENT.FiniteCertificates.PackedRange31To149
public import ENT.Certificate.KroneckerSoundness
public import ENT.Spline.PureCertificateBridge
public import ENT.Comparison.CurvatureToENT
public import ENT.IIDAE

/-! Finite-dimensional entropy comparison and equality through dimension 149. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace ENT

theorem cellwise_curvature_seven_through_149 (n : ℕ)
    (hn0 : 7 ≤ n) (hn1 : n ≤ 149) : Spline.CellwiseCurvature n := by
  by_cases h30 : n ≤ 30
  · exact FiniteCertificates.cellwise_curvature_seven_through_thirty n hn0 h30
  · apply Spline.cellwiseCurvature_of_pure_prop_family n (by omega)
      FiniteCertificates.PackedValid
    · intro c h
      obtain ⟨rBase,bBase,hvalid⟩ := h
      exact Certificate.Kronecker.valid_sound c rBase bBase hvalid
    · exact FiniteCertificates.family_packed_31_149 n (by omega) hn1

theorem ent_of_dimension_seven_through_149 {n : ℕ}
    (hn0 : 7 ≤ n) (hn1 : n ≤ 149) : ENTAt n :=
  entAt_of_cellwise_curvature (by omega)
    (cellwise_curvature_seven_through_149 n hn0 hn1)

universe u
theorem iid_ent_of_dimension_seven_through_149_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn0 : 7 ≤ n) (hn1 : n ≤ 149)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha
    (ent_of_dimension_seven_through_149 hn0 hn1)

end ENT
