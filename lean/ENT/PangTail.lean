module

public import ENT.Pang.LargeNCurvature
public import ENT.Comparison.CurvatureToENT
public import ENT.IIDAE

/-! Pang’s large-dimensional entropy comparison from the curvature estimate on the diagonal density. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT
noncomputable section

theorem ent_of_dimension_ge_150 {n : ℕ} (hn : 150 ≤ n) : ENTAt n :=
  entAt_of_spline_curvature (by omega) (Pang.pang_large_n_curvature_nonneg hn)

theorem pang_tail : PangTail := fun _ hn => ent_of_dimension_ge_150 hn

universe u

theorem iid_ent_of_dimension_ge_150_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 150 ≤ n)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) :=
  iid_ent_of_entAt_ae μ U hU hind hlaw a ha (ent_of_dimension_ge_150 hn)

end
end ENT
