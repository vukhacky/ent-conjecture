module

public import ENT.Small.FiveSixLocal
public import ENT.Small.RemainderFive
public import ENT.Small.EnclosuresFive
public import ENT.Small.SlackFive
public import ENT.Small.Assembly
public import ENT.IIDAE

/-! Entropy comparison and equality for the stated small dimension. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT
noncomputable section

theorem dimension5_entropy_gap (a : Fin 5 → ℝ) (ha : IsUnit a) :
    deficit a/1000≤(Spline.diagonalFiniteEntropyDensity 5 (by decide)).entropy-
      (projectionFiniteEntropyDensity a ha).entropy := by
  by_cases hδ : deficit a≤7/12500
  · let b : Fin 5 → ℝ := fun i=>|a i|
    have hb : IsUnit b := (isUnit_abs_iff a).mpr ha
    have hbδ : deficit b=deficit a := by simp only [b,deficit,sq_abs]
    obtain ⟨H,hM⟩ := Small.logThirdEnvelope_five_bound
    have h := Small.five_local_entropy_gap_of_enclosures H hM Small.smallKappa_five_lower
      b hb (fun i=>abs_nonneg (a i))
      (by rw [hbδ]; exact hδ) (projectionFiniteEntropyDensity b hb)
    have heq : (projectionFiniteEntropyDensity b hb).entropy=
        (projectionFiniteEntropyDensity a ha).entropy := by
      have h := ((projectionFiniteEntropyDensity b hb).transport (projectionLaw_abs a)).entropy_eq
        (projectionFiniteEntropyDensity a ha)
      simpa only [FiniteEntropyDensity.entropy_transport] using h
    simpa only [hbδ,heq] using h
  · exact Small.exterior_five_of_sigma_bound Small.sigma5_lt.le a ha (le_of_not_ge hδ)

theorem ent_five : ENTAt 5 := by
  apply entAt_of_positive_deficit_gap (Spline.diagonalFiniteEntropyDensity 5 (by decide))
    (by norm_num : (0:ℝ)<1/1000)
  intro a ha
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using dimension5_entropy_gap a ha

universe u

theorem iid_ent_five_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Fin 5 → Ω → ℝ) (hU : ∀ i,AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i,μ.map (U i)=uniformUnit)
    (a : Fin 5 → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω=>∑ i,a i*U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω=>(Real.sqrt 5)⁻¹*∑ i,U i ω)),
      p.entropy≤q.entropy ∧ (p.entropy=q.entropy↔IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha ent_five

end
end ENT
