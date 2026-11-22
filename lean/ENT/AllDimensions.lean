module

public import ENT.ThroughThirty
public import ENT.MediumDimensions149
public import ENT.PangTail
public import ENT.Assembly

/-! Entropy comparison and equality in all dimensions, combining the finite proof through dimension 149 with the analytic bound from dimension 150. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT

theorem finite_ent : FiniteStatement := by
  intro n hn hn149
  by_cases hn30 : n ≤ 30
  · exact ent_of_dimension_le_thirty hn hn30
  · exact ent_of_dimension_seven_through_149 (by omega) hn149

theorem ent_conjecture : MainStatement :=
  assembleAllDimensions finite_ent pang_tail

/-- The conclusion holds for every actual finite-entropy density representative
of the two laws, not only the witnesses supplied by `ent_conjecture`. -/
theorem ent_conjecture_for_densities {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : IsUnit a)
    (p : FiniteEntropyDensity (projectionLaw a))
    (q : FiniteEntropyDensity (projectionLaw (diagonal n))) :
    p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) := by
  obtain ⟨p₀, q₀, h⟩ := ent_conjecture n hn a ha
  rw [p.entropy_eq p₀, q.entropy_eq q₀]
  exact h

universe u

theorem iid_ent_conjecture_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity
      (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha (ent_conjecture n hn)

theorem iid_ent_conjecture_for_densities_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a)
    (p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)))
    (q : FiniteEntropyDensity
      (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω))) :
    p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) := by
  obtain ⟨p₀, q₀, h⟩ := iid_ent_conjecture_ae μ hn U hU hind hlaw a ha
  rw [p.entropy_eq p₀, q.entropy_eq q₀]
  exact h

end ENT
