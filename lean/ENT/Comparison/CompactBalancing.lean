module

public import ENT.Comparison.BalancingWeights
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.FunProp

/-!
Pair balancing implies maximization at flat weights for a continuous functional.
The proof minimizes the quadratic energy on the compact superlevel set through
the starting point.  This is a finite-dimensional alternative to constructing
an infinite balancing sequence; the pair comparison itself remains a separate
analytic hypothesis, explicitly present in the theorem's type.
-/

@[expose] public section

set_option autoImplicit false
open Set
open scoped BigOperators

namespace ENT.Comparison

noncomputable section

def weightSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

def flatWeights (n : ℕ) : Fin n → ℝ := fun _ => (n : ℝ)⁻¹

theorem flatWeights_mem_weightSimplex {n : ℕ} (hn : 0 < n) :
    flatWeights n ∈ weightSimplex n := by
  constructor
  · intro i
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [flatWeights, nsmul_eq_mul, hnR]

theorem isClosed_weightSimplex (n : ℕ) : IsClosed (weightSimplex n) := by
  have heq : weightSimplex n =
      (⋂ i : Fin n, {w : Fin n → ℝ | 0 ≤ w i}) ∩
        {w : Fin n → ℝ | ∑ i, w i = 1} := by
    ext w
    simp only [weightSimplex, mem_setOf_eq, mem_inter_iff, mem_iInter]
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  · exact isClosed_eq (by fun_prop) continuous_const

theorem weightSimplex_subset_Icc (n : ℕ) :
    weightSimplex n ⊆ Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1) := by
  intro w hw
  refine ⟨hw.1, ?_⟩
  intro i
  have h := Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
  simpa only [hw.2] using h

theorem isCompact_weightSimplex (n : ℕ) : IsCompact (weightSimplex n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_weightSimplex n) (weightSimplex_subset_Icc n)

theorem balanceWeights_mem_weightSimplex {n : ℕ} {w : Fin n → ℝ}
    (hw : w ∈ weightSimplex n) (i j : Fin n) (hij : i ≠ j) :
    balanceWeights w i j ∈ weightSimplex n := by
  refine ⟨balanceWeights_nonneg w i j hw.1, ?_⟩
  rw [sum_balanceWeights w i j hij, hw.2]

theorem continuous_weightEnergy (n : ℕ) (c : ℝ) :
    Continuous (fun w : Fin n → ℝ => weightEnergy w c) := by
  unfold weightEnergy
  fun_prop

/-- A continuous functional that does not decrease under any pair balancing
attains its maximal value at the flat weight vector. -/
theorem le_flat_of_pair_balancing {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : ContinuousOn F (weightSimplex n))
    (hpair : ∀ w ∈ weightSimplex n, ∀ i j : Fin n, i ≠ j →
      F w ≤ F (balanceWeights w i j))
    (w₀ : Fin n → ℝ) (hw₀ : w₀ ∈ weightSimplex n) :
    F w₀ ≤ F (flatWeights n) := by
  let S : Set (Fin n → ℝ) := weightSimplex n ∩ F ⁻¹' Ici (F w₀)
  have hSclosed : IsClosed S :=
    hF.preimage_isClosed_of_isClosed (isClosed_weightSimplex n) isClosed_Ici
  have hScompact : IsCompact S :=
    (isCompact_weightSimplex n).of_isClosed_subset hSclosed inter_subset_left
  have hSne : S.Nonempty := ⟨w₀, hw₀, le_rfl⟩
  obtain ⟨w, hwS, hmin⟩ := hScompact.exists_isMinOn hSne
    (continuous_weightEnergy n (n : ℝ)⁻¹).continuousOn
  have hw : w ∈ weightSimplex n := hwS.1
  have hequal : ∀ i j : Fin n, w i = w j := by
    intro i j
    by_contra hne
    have hij : i ≠ j := fun h => hne (congrArg w h)
    have hbalanced : balanceWeights w i j ∈ S :=
      ⟨balanceWeights_mem_weightSimplex hw i j hij,
        le_trans hwS.2 (hpair w hw i j hij)⟩
    have henergy := (isMinOn_iff.mp hmin) (balanceWeights w i j) hbalanced
    rw [weightEnergy_balanceWeights w i j hij (n : ℝ)⁻¹] at henergy
    have hsq : 0 < (w i - w j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    nlinarith
  have hwflat : w = flatWeights n := by
    funext i
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsum : (n : ℝ) * w i = 1 := by
      calc
        (n : ℝ) * w i = ∑ _k : Fin n, w i := by simp
        _ = ∑ k : Fin n, w k := Finset.sum_congr rfl (fun k _ => (hequal k i).symm)
        _ = 1 := hw.2
    exact mul_left_cancel₀ hnR (hsum.trans (mul_inv_cancel₀ hnR).symm)
  rw [← hwflat]
  exact hwS.2

end
end ENT.Comparison
