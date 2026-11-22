module

public import ENT.Small.FourLocal
public import ENT.Small.EnclosuresFourBounds
public import ENT.Small.SlackFour
public import ENT.Small.Assembly
public import ENT.IIDAE

/-! Entropy comparison and equality in dimension four, allowing arbitrary signs and zero coefficients. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT
noncomputable section

theorem dimension4_entropy_gap (a : Fin 4 → ℝ) (ha : IsUnit a) :
    deficit a/1000≤(Spline.diagonalFiniteEntropyDensity 4 (by decide)).entropy-
      (projectionFiniteEntropyDensity a ha).entropy := by
  by_cases hδ : deficit a≤1/500
  · let b : Fin 4 → ℝ := fun i=>|a i|
    have hb : IsUnit b := (isUnit_abs_iff a).mpr ha
    have hbδ : deficit b=deficit a := by simp only [b,deficit,sq_abs]
    have h := Small.four_local_entropy_gap_of_scalar_bounds Small.fourLocalScalarBounds b hb (fun i=>abs_nonneg (a i))
      (by rw [hbδ]; exact hδ) (projectionFiniteEntropyDensity b hb)
    have heq : (projectionFiniteEntropyDensity b hb).entropy=
        (projectionFiniteEntropyDensity a ha).entropy := by
      have h := ((projectionFiniteEntropyDensity b hb).transport (projectionLaw_abs a)).entropy_eq
        (projectionFiniteEntropyDensity a ha)
      simpa only [FiniteEntropyDensity.entropy_transport] using h
    rw [hbδ,heq] at h
    linarith [deficit_nonneg a]
  · exact Small.exterior_four_of_sigma_bound Small.sigma4_lt.le a ha (le_of_not_ge hδ)

theorem ent_four : ENTAt 4 := by
  apply entAt_of_positive_deficit_gap (Spline.diagonalFiniteEntropyDensity 4 (by decide))
    (by norm_num : (0:ℝ)<1/1000)
  intro a ha
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using dimension4_entropy_gap a ha

universe u

theorem iid_ent_four_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Fin 4 → Ω → ℝ) (hU : ∀ i,AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i,μ.map (U i)=uniformUnit)
    (a : Fin 4 → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω=>∑ i,a i*U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω=>(Real.sqrt 4)⁻¹*∑ i,U i ω)),
      p.entropy≤q.entropy ∧ (p.entropy=q.entropy↔IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha ent_four

end
end ENT
