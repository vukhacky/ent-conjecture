module

public import ENT.Quantitative.LargeStability
public import ENT.Quantitative.LargeCurvature150

/-! Global stability from the finite certificates and the analytic threshold-150 refinement. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace ENT.Quantitative
noncomputable section

theorem kl_stability_ge_150 {n : ℕ} (hn : 150≤n) :
    KLStabilityAt n (7/(180*(n:ℝ))) :=
  klStabilityAt_of_curvature (by omega) 7 (large_curvature_ge_150 hn)

/-- The uniform explicit coefficient for every dimension at least seven. -/
theorem kl_stability_ge_seven {n : ℕ} (hn : 7≤n) :
    KLStabilityAt n (7/(180*(n:ℝ))) := by
  by_cases hsmall : n≤149
  · exact kl_stability_seven_through_149 hn hsmall
  · exact kl_stability_ge_150 (by omega)

theorem entropy_stability_ge_seven {n : ℕ} (hn : 7≤n) :
    EntropyStabilityAt n (7/(180*(n:ℝ))) :=
  (kl_stability_ge_seven hn).entropyStabilityAt

/-- The manuscript's dimension-dependent explicit linear stability bound. -/
theorem entropy_stability_ge_three {n : ℕ} (hn : 3≤n) :
    EntropyStabilityAt n (if n≤6 then 1/1000 else 7/(180*(n:ℝ))) := by
  by_cases hsmall : n≤6
  · rw [if_pos hsmall]
    exact entropy_stability_three_through_six hn hsmall
  · rw [if_neg hsmall]
    exact entropy_stability_ge_seven (by omega)

universe u

theorem iid_kl_stability_ge_seven_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 7≤n)
    (U : Fin n→Ω→ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i)=uniformUnit)
    (a : Fin n→ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω=>∑ i,a i*U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω=>(Real.sqrt (n:ℝ))⁻¹*∑ i,U i ω)),
    ∃ hKL : FiniteKLData p q,
      (7/(180*(n:ℝ)))*deficit a+hKL.klDivergence≤q.entropy-p.entropy :=
  iid_kl_stability_of_ae μ U hU hind hlaw (kl_stability_ge_seven hn) a ha

theorem iid_entropy_stability_ge_three_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 3≤n)
    (U : Fin n→Ω→ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i)=uniformUnit)
    (a : Fin n→ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω=>∑ i,a i*U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω=>(Real.sqrt (n:ℝ))⁻¹*∑ i,U i ω)),
      (if n≤6 then 1/1000 else 7/(180*(n:ℝ)))*deficit a≤q.entropy-p.entropy :=
  iid_entropy_stability_of_ae μ U hU hind hlaw (entropy_stability_ge_three hn) a ha

end
end ENT.Quantitative
