module

public import ENT.Historical.BalancingSequence
public import ENT.Comparison.CurvatureExpectation

/-! Pair balancing yields global comparison by iteratively averaging the largest and smallest squared coefficients. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace ENT.Comparison
noncomputable section

theorem extremeBalance_function_le {n : ℕ} (hn : 0 < n) {F : (Fin n → ℝ) → ℝ}
    (hpair : ∀ w ∈ weightSimplex n, ∀ i j : Fin n, i ≠ j →
      F w ≤ F (balanceWeights w i j))
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) :
    F w ≤ F (extremeBalance hn w) := by
  by_cases hij : maxWeightIndex hn w = minWeightIndex hn w
  · simp only [extremeBalance, hij, balanceWeights_self, le_refl]
  · exact hpair w hw _ _ hij

theorem balancingSequence_function_monotone {n : ℕ} (hn : 0 < n)
    {F : (Fin n → ℝ) → ℝ}
    (hpair : ∀ w ∈ weightSimplex n, ∀ i j : Fin n, i ≠ j →
      F w ≤ F (balanceWeights w i j))
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) :
    Monotone (fun m => F (balancingSequence hn w m)) := by
  apply monotone_nat_of_le_succ
  intro m
  exact extremeBalance_function_le hn hpair _ (balancingSequence_mem hn hw m)

theorem le_flat_of_pair_balancing_iteration {n : ℕ} (hn : 0 < n)
    {F : (Fin n → ℝ) → ℝ} (hF : Continuous F)
    (hpair : ∀ w ∈ weightSimplex n, ∀ i j : Fin n, i ≠ j →
      F w ≤ F (balanceWeights w i j))
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) :
    F w ≤ F (flatWeights n) := by
  have hlim := hF.continuousAt.tendsto.comp (balancingSequence_tendsto hn hw)
  apply ge_of_tendsto hlim
  exact Filter.Eventually.of_forall fun m =>
    balancingSequence_function_monotone hn hpair w hw (Nat.zero_le m)

theorem expectation_le_flat_by_iteration {n : ℕ} (hn : 0 < n)
    {V : ℝ → ℝ} (hV : Continuous V) {C : ℝ} (hC : ∀ x, ‖V x‖ ≤ C)
    (hpair : ∀ w ∈ weightSimplex n, ∀ i j : Fin n, i ≠ j →
      weightExpectation V w ≤ weightExpectation V (balanceWeights w i j))
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) :
    weightExpectation V w ≤ weightExpectation V (flatWeights n) :=
  le_flat_of_pair_balancing_iteration hn (continuous_weightExpectation hV hC) hpair w hw

namespace EvenJet

theorem weight_expectation_le_flat_by_iteration {n : ℕ} (hn : 0 < n)
    {R : ℝ} {g : ℝ → ℝ} (J : EvenJet R g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) (hR : Real.sqrt n < R)
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) :
    weightExpectation g w ≤ weightExpectation g (flatWeights n) :=
  expectation_le_flat_by_iteration hn J.continuous hC
    (J.weight_pair_comparison hC hR) w hw

theorem expectation_le_diagonal_by_iteration {n : ℕ} (hn : 0 < n)
    {R : ℝ} {g : ℝ → ℝ} (J : EvenJet R g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) (hR : Real.sqrt n < R)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    potentialExpectation g a ≤ potentialExpectation g (diagonal n) := by
  have hw : (fun i => (a i) ^ 2) ∈ weightSimplex n :=
    ⟨fun i => sq_nonneg (a i), ha⟩
  have h := J.weight_expectation_le_flat_by_iteration hn hC hR _ hw
  have hleft : weightExpectation g (fun i => (a i) ^ 2) = potentialExpectation g a := by
    unfold weightExpectation
    simp_rw [Real.sqrt_sq_eq_abs]
    rw [potentialExpectation_eq_integral_law _ J.continuous,
      projectionLaw_abs a, ← potentialExpectation_eq_integral_law _ J.continuous]
  have hright : weightExpectation g (flatWeights n) = potentialExpectation g (diagonal n) := by
    unfold weightExpectation flatWeights diagonal
    simp only [Real.sqrt_inv]
  rwa [hleft, hright] at h

end EvenJet

namespace CurvaturePotential

variable {n : ℕ} {V : ℝ → ℝ} (J : CurvaturePotential (Real.sqrt n) V)

include J

theorem contracted_expectation_le_by_iteration (hn : 0 < n)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, corrected V (ρ * x) ∂projectionLaw a) ≤
      ∫ x, corrected V (ρ * x) ∂projectionLaw (diagonal n) := by
  let K := J.contractionJet ρ hρ0 hρ1
  obtain ⟨C, hC⟩ := J.contraction_bounded ρ hρ0 hρ1
  have h := K.expectation_le_diagonal_by_iteration hn hC (J.clipRadius_gt ρ hρ0 hρ1) a ha
  rw [potentialExpectation_eq_integral_law _ K.continuous,
    potentialExpectation_eq_integral_law _ K.continuous] at h
  have heq (b : Fin n → ℝ) (hb : IsUnit b) :
      (∫ x, clipped V ρ (clipRadius (Real.sqrt n) ρ) x ∂projectionLaw b) =
        ∫ x, corrected V (ρ * x) ∂projectionLaw b := by
    apply integral_congr_ae
    apply (projectionLaw_ae_mem b).mono
    intro x hx
    have hR := projectionRadius_le_sqrt b hb
    exact J.contraction_eq ρ hρ0 hρ1
      ⟨(neg_le_neg hR).trans hx.1, hx.2.trans hR⟩
  rwa [heq a ha, heq (diagonal n) (isUnit_diagonal hn)] at h

/-- Fixed-rho bounded-convergence step for the actual prescribed iteration.
The globally clipped integrand agrees with the contracted potential on every
unit projection, so its established dominated-convergence theorem applies. -/
theorem contracted_balancing_expectation_tendsto (hn : 0 < n)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) :
    Tendsto (fun m => ∫ x, corrected V (ρ * x)
      ∂projectionLaw (fun i => Real.sqrt (balancingSequence hn w m i))) atTop
      (𝓝 (∫ x, corrected V (ρ * x) ∂projectionLaw (diagonal n))) := by
  let K := J.contractionJet ρ hρ0 hρ1
  obtain ⟨C, hC⟩ := J.contraction_bounded ρ hρ0 hρ1
  have hlim := balancingSequence_expectation_tendsto hn hw K.continuous hC
  have heq (v : Fin n → ℝ) (hv : v ∈ weightSimplex n) :
      weightExpectation (clipped V ρ (clipRadius (Real.sqrt n) ρ)) v =
        ∫ x, corrected V (ρ * x) ∂projectionLaw (fun i => Real.sqrt (v i)) := by
    unfold weightExpectation
    rw [potentialExpectation_eq_integral_law _ K.continuous]
    apply integral_congr_ae
    apply (projectionLaw_ae_mem (fun i => Real.sqrt (v i))).mono
    intro x hx
    have hvu : IsUnit (fun i => Real.sqrt (v i)) := by
      unfold IsUnit
      simpa only [Real.sq_sqrt (hv.1 _)] using hv.2
    have hR := projectionRadius_le_sqrt (fun i => Real.sqrt (v i)) hvu
    exact J.contraction_eq ρ hρ0 hρ1
      ⟨(neg_le_neg hR).trans hx.1, hx.2.trans hR⟩
  have hright : weightExpectation (clipped V ρ (clipRadius (Real.sqrt n) ρ)) (flatWeights n) =
      ∫ x, corrected V (ρ * x) ∂projectionLaw (diagonal n) := by
    rw [heq (flatWeights n) (flatWeights_mem_weightSimplex hn)]
    simp only [flatWeights, Real.sqrt_inv]
    rfl
  simp_rw [heq _ (balancingSequence_mem hn hw _), hright] at hlim
  exact hlim

theorem corrected_expectation_le_by_iteration (hn : 0 < n)
    (hdiag : ∀ᵐ x ∂projectionLaw (diagonal n), x ∈ Ioo (-Real.sqrt n) (Real.sqrt n))
    (hV : Integrable V (projectionLaw (diagonal n))) (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, corrected V x ∂projectionLaw a) ≤
      ∫ x, corrected V x ∂projectionLaw (diagonal n) := by
  have hbound : ∀ᶠ m in atTop, radialSequence m ∈ Icc 0 1 :=
    Filter.Eventually.of_forall fun m =>
      ⟨(radialSequence_mem m).1, (radialSequence_mem m).2.le⟩
  have hp := J.corrected_integral_tendsto (J.projection_ae_interior hn hdiag a ha)
    (J.projection_integrable hn hV a ha) radialSequence hbound radialSequence_tendsto
  have hq := J.corrected_integral_tendsto hdiag hV radialSequence hbound radialSequence_tendsto
  exact le_of_tendsto_of_tendsto' hp hq fun m =>
    J.contracted_expectation_le_by_iteration hn _ (radialSequence_mem m).1
      (radialSequence_mem m).2 a ha

theorem expectation_le_by_iteration (hn : 0 < n)
    (hdiag : ∀ᵐ x ∂projectionLaw (diagonal n), x ∈ Ioo (-Real.sqrt n) (Real.sqrt n))
    (hV : Integrable V (projectionLaw (diagonal n))) (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, V x ∂projectionLaw a) ≤ ∫ x, V x ∂projectionLaw (diagonal n) := by
  apply (J.integral_corrected_le_iff (J.projection_ae_interior hn hdiag a ha) hdiag
    (J.projection_integrable hn hV a ha) hV ?_).mp
  · exact J.corrected_expectation_le_by_iteration hn hdiag hV a ha
  · rw [integral_projectionLaw_sq_of_isUnit a ha,
      integral_projectionLaw_sq_of_isUnit (diagonal n) (isUnit_diagonal hn)]

end CurvaturePotential

end
end ENT.Comparison
