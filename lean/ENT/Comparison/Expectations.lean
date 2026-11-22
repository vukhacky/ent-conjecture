module

public import ENT.Basic.Uniform
public import ENT.Comparison.CompactBalancing
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Tactic.FunProp

/-! Continuity of the expectation of a bounded continuous potential as the coefficient vector varies, by dominated convergence under the product law. -/

@[expose] public section

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ENT.Comparison

noncomputable section

def potentialExpectation {n : ℕ} (V : ℝ → ℝ) (a : Fin n → ℝ) : ℝ :=
  ∫ x, V (projection a x) ∂cubeLaw n

def weightExpectation {n : ℕ} (V : ℝ → ℝ) (w : Fin n → ℝ) : ℝ :=
  potentialExpectation V (fun i => Real.sqrt (w i))

theorem integrable_bounded_potential {n : ℕ} {V : ℝ → ℝ}
    (hV : Continuous V) {C : ℝ} (hC : ∀ x, ‖V x‖ ≤ C) (a : Fin n → ℝ) :
    Integrable (fun x => V (projection a x)) (cubeLaw n) := by
  apply Integrable.of_bound (hV.comp (continuous_projection a)).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun x => hC (projection a x))

theorem continuous_potentialExpectation {n : ℕ} {V : ℝ → ℝ}
    (hV : Continuous V) {C : ℝ} (hC : ∀ x, ‖V x‖ ≤ C) :
    Continuous (potentialExpectation (n := n) V) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro a
    exact (hV.comp (continuous_projection a)).aestronglyMeasurable
  · intro a
    exact Filter.Eventually.of_forall (fun x => hC (projection a x))
  · exact integrable_const C
  · apply Filter.Eventually.of_forall
    intro x
    apply hV.comp
    unfold projection
    fun_prop

theorem continuous_weightExpectation {n : ℕ} {V : ℝ → ℝ}
    (hV : Continuous V) {C : ℝ} (hC : ∀ x, ‖V x‖ ≤ C) :
    Continuous (weightExpectation (n := n) V) := by
  apply (continuous_potentialExpectation hV hC).comp
  fun_prop

/-- Pair balancing and bounded continuous test functions imply the global expectation comparison. -/
theorem expectation_le_flat_of_pair_balancing {n : ℕ} (hn : 0 < n)
    {V : ℝ → ℝ} (hV : Continuous V) {C : ℝ} (hC : ∀ x, ‖V x‖ ≤ C)
    (hpair : ∀ w ∈ weightSimplex n, ∀ i j : Fin n, i ≠ j →
      weightExpectation V w ≤ weightExpectation V (balanceWeights w i j))
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) :
    weightExpectation V w ≤ weightExpectation V (flatWeights n) := by
  exact le_flat_of_pair_balancing hn (weightExpectation V)
    (continuous_weightExpectation hV hC).continuousOn hpair w hw

end
end ENT.Comparison
