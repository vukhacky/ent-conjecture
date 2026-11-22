module

public import ENT.Quantitative.Curvature
public import ENT.Quantitative.StabilityDefinitions
public import ENT.FiniteCurvature149
public import ENT.DimensionThree
public import ENT.DimensionFour
public import ENT.DimensionFive
public import ENT.DimensionSix

/-! Quantitative stability from the finite certificates through dimension 149, including independent variables on arbitrary probability spaces. -/

@[expose] public section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ENT.Quantitative
noncomputable section

theorem klStabilityAt_of_curvature {n : ℕ} (hn : 5 ≤ n) (b : ℝ)
    (hcurv : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt n),
      (b / (n : ℝ)) * x ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x) :
    KLStabilityAt n (b / (180 * (n : ℝ))) := by
  intro a ha
  refine ⟨projectionFiniteEntropyDensity a ha,
    Spline.diagonalFiniteEntropyDensity n (by omega),
    Small.unitProjectionFiniteKLData (by omega) a ha (projectionFiniteEntropyDensity a ha), ?_⟩
  have h := curvature_entropy_gap hn b hcurv a ha (projectionFiniteEntropyDensity a ha)
  convert h using 1 <;> ring

theorem kl_stability_seven_through_149 {n : ℕ} (hn0 : 7 ≤ n) (hn1 : n ≤ 149) :
    KLStabilityAt n (7 / (180 * (n : ℝ))) := by
  apply klStabilityAt_of_curvature (by omega) 7
  intro x hx
  exact diagonal_density_curvature_seven_through_149 hn0 hn1 x hx.1.le hx.2

theorem entropy_stability_seven_through_149 {n : ℕ} (hn0 : 7 ≤ n) (hn1 : n ≤ 149) :
    EntropyStabilityAt n (7 / (180 * (n : ℝ))) :=
  (kl_stability_seven_through_149 hn0 hn1).entropyStabilityAt

theorem entropy_stability_three_through_six {n : ℕ} (hn0 : 3 ≤ n) (hn1 : n ≤ 6) :
    EntropyStabilityAt n (1 / 1000) := by
  intro a ha
  refine ⟨projectionFiniteEntropyDensity a ha,
    Spline.diagonalFiniteEntropyDensity n (by omega), ?_⟩
  have h : deficit a / 1000 ≤
      (Spline.diagonalFiniteEntropyDensity n (by omega)).entropy -
        (projectionFiniteEntropyDensity a ha).entropy := by
    interval_cases n
    · exact dimension3_entropy_gap a ha
    · exact dimension4_entropy_gap a ha
    · exact dimension5_entropy_gap a ha
    · exact dimension6_entropy_gap a ha
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

theorem stability_seven_through_149_for_densities {n : ℕ}
    (hn0 : 7 ≤ n) (hn1 : n ≤ 149)
    (a : Fin n → ℝ) (ha : IsUnit a)
    (p : FiniteEntropyDensity (projectionLaw a)) :
    7 * deficit a / (180 * (n : ℝ)) +
        (Small.unitProjectionFiniteKLData (by omega) a ha p).klDivergence ≤
      (Spline.diagonalFiniteEntropyDensity n (by omega)).entropy - p.entropy := by
  apply curvature_entropy_gap (by omega) 7 _ a ha p
  intro x hx
  exact diagonal_density_curvature_seven_through_149 hn0 hn1 x hx.1.le hx.2

universe u

theorem iid_kl_stability_seven_through_149_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn0 : 7 ≤ n) (hn1 : n ≤ 149)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
    ∃ hKL : FiniteKLData p q,
      (7 / (180 * (n : ℝ))) * deficit a + hKL.klDivergence ≤ q.entropy - p.entropy :=
  iid_kl_stability_of_ae μ U hU hind hlaw (kl_stability_seven_through_149 hn0 hn1) a ha

theorem iid_entropy_stability_three_through_six_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn0 : 3 ≤ n) (hn1 : n ≤ 6)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω => ∑ i, a i * U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)),
      (1 / 1000 : ℝ) * deficit a ≤ q.entropy - p.entropy :=
  iid_entropy_stability_of_ae μ U hU hind hlaw
    (entropy_stability_three_through_six hn0 hn1) a ha

end
end ENT.Quantitative
