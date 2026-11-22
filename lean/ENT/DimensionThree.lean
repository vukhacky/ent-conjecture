module

public import ENT.Small.ThreePrimitives
public import ENT.Small.SlackThree
public import ENT.Small.Assembly
public import ENT.IIDAE

/-! Closed three-dimensional ENT, including all signs, zero coefficients,
finite actual entropy and the precise equality characterization. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT
noncomputable section

theorem dimension3_entropy_gap (a : Fin 3 → ℝ) (ha : IsUnit a) :
    deficit a/1000≤(Spline.diagonalFiniteEntropyDensity 3 (by decide)).entropy-
      (projectionFiniteEntropyDensity a ha).entropy := by
  by_cases hδ : deficit a≤1/100
  · let b : Fin 3 → ℝ := fun i=>|a i|
    have hb : IsUnit b := (isUnit_abs_iff a).mpr ha
    have hbδ : deficit b=deficit a := by simp only [b,deficit,sq_abs]
    have h := Small.three_local_entropy_gap b hb (fun i=>abs_nonneg (a i))
      (by rw [hbδ]; exact hδ) (projectionFiniteEntropyDensity b hb)
    have heq : (projectionFiniteEntropyDensity b hb).entropy=
        (projectionFiniteEntropyDensity a ha).entropy := by
      have h := ((projectionFiniteEntropyDensity b hb).transport (projectionLaw_abs a)).entropy_eq
        (projectionFiniteEntropyDensity a ha)
      simpa only [FiniteEntropyDensity.entropy_transport] using h
    rw [hbδ,heq] at h
    linarith [deficit_nonneg a]
  · exact Small.exterior_three_of_sigma_bound Small.sigma3_lt.le a ha (le_of_not_ge hδ)

theorem ent_three : ENTAt 3 := by
  apply entAt_of_positive_deficit_gap (Spline.diagonalFiniteEntropyDensity 3 (by decide))
    (by norm_num : (0:ℝ)<1/1000)
  intro a ha
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using dimension3_entropy_gap a ha

universe u

theorem iid_ent_three_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Fin 3 → Ω → ℝ) (hU : ∀ i,AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i,μ.map (U i)=uniformUnit)
    (a : Fin 3 → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω=>∑ i,a i*U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω=>(Real.sqrt 3)⁻¹*∑ i,U i ω)),
      p.entropy≤q.entropy ∧ (p.entropy=q.entropy↔IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha ent_three

end
end ENT
