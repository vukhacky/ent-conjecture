module

public import ENT.Comparison.FiniteAverage
public import ENT.Comparison.SupportRadius
public import ENT.Basic.Symmetry
public import ENT.Basic.Independence

/-! Pair balancing with the actual residual independent sum, followed by
compact maximization on the simplex of squared coefficients. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace ENT.Comparison
noncomputable section

theorem potentialExpectation_pair_swap {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    potentialExpectation g ![a, b] = potentialExpectation g ![b, a] := by
  have hs : projectionLaw ![b, a] = projectionLaw ![a, b] := by
    convert projectionLaw_two_swap ![a, b] using 1
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [potentialExpectation_eq_integral_law _ hg,
    potentialExpectation_eq_integral_law _ hg, hs]

theorem potentialExpectation_remove_pair {n : ℕ} {g : ℝ → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (a : Fin (n + 2) → ℝ)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    potentialExpectation g a =
      potentialExpectation (finiteAverage g (removeCoefficient (removeCoefficient a i) j))
        ![a i, a (i.succAbove j)] := by
  rw [potentialExpectation_eq_finiteAverage,
    finiteAverage_remove hg hC a i,
    finiteAverage_remove hg hC (removeCoefficient a i) j,
    potentialExpectation_eq_finiteAverage,
    finiteAverage_two (continuous_finiteAverage hg hC _)
      (finiteAverage_norm_le hC _)]
  rfl

namespace EvenJet

theorem pair_comparison_nonneg {R : ℝ} {g : ℝ → ℝ} (J : EvenJet R g)
    {a b c C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsq : 2 * c ^ 2 = a ^ 2 + b ^ 2) (hR : 2 * c ≤ R)
    (hC : ∀ x, ‖g x‖ ≤ C) :
    potentialExpectation g ![a, b] ≤ potentialExpectation g ![c, c] := by
  by_cases hz : c = 0
  · have ha0 : a = 0 := by nlinarith [sq_nonneg b]
    have hb0 : b = 0 := by nlinarith [sq_nonneg a]
    simp only [hz, ha0, hb0]
    exact le_rfl
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hz)
    rcases le_total b a with hba | hab
    · exact J.pair_comparison hb hba hcpos hsq hR hC
    · rw [potentialExpectation_pair_swap J.continuous a b]
      exact J.pair_comparison ha hab hcpos (by linarith [hsq]) hR hC

theorem weight_pair_succ {n : ℕ} {R : ℝ} {g : ℝ → ℝ} (J : EvenJet R g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hR : Real.sqrt (n + 2 : ℕ) < R)
    (w : Fin (n + 2) → ℝ) (hw : w ∈ weightSimplex (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    weightExpectation g w ≤ weightExpectation g (balanceWeights w i (i.succAbove j)) := by
  let a : Fin (n + 2) → ℝ := fun k => Real.sqrt (w k)
  let v := balanceWeights w i (i.succAbove j)
  let b : Fin (n + 2) → ℝ := fun k => Real.sqrt (v k)
  let r := removeCoefficient (removeCoefficient a i) j
  let c := Real.sqrt ((w i + w (i.succAbove j)) / 2)
  have hij : i ≠ i.succAbove j := (Fin.succAbove_ne i j).symm
  have hv : v ∈ weightSimplex (n + 2) := balanceWeights_mem_weightSimplex hw i _ hij
  have hb0 : b i = c := by simp [b, v, balanceWeights, c]
  have hb1 : b (i.succAbove j) = c := by
    simp [b, v, balanceWeights, Fin.succAbove_ne, c]
  have hres : removeCoefficient (removeCoefficient b i) j = r := by
    funext k
    have hne0 := Fin.succAbove_ne i (j.succAbove k)
    have hne1 : i.succAbove (j.succAbove k) ≠ i.succAbove j :=
      fun h => Fin.succAbove_ne j k (Fin.succAbove_right_injective h)
    simp [r, a, b, v, removeCoefficient, balanceWeights, hne0, hne1]
  have hsum : (∑ k, b k) = 2 * c + ∑ k, r k := by
    rw [Fin.sum_univ_succAbove b i]
    change b i + (∑ k, removeCoefficient b i k) = _
    rw [Fin.sum_univ_succAbove (removeCoefficient b i) j]
    change b i + (b (i.succAbove j) + ∑ k,
      removeCoefficient (removeCoefficient b i) j k) = _
    rw [hres, hb0, hb1]
    ring
  have hbound : 2 * c + ∑ k, r k < R := by
    rw [← hsum]
    exact lt_of_le_of_lt (sum_sqrt_weights_le hv) hR
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hr : ∀ k, 0 ≤ r k := fun k => Real.sqrt_nonneg _
  have hrR : (∑ k, r k) < R := by linarith
  have K := J.finite_average hC r hr hrR
  have hsq : 2 * c ^ 2 = (a i) ^ 2 + (a (i.succAbove j)) ^ 2 := by
    have hm : 0 ≤ (w i + w (i.succAbove j)) / 2 :=
      div_nonneg (add_nonneg (hw.1 i) (hw.1 (i.succAbove j))) (by norm_num)
    simp only [c, a, Real.sq_sqrt hm, Real.sq_sqrt (hw.1 _)]
    ring
  change potentialExpectation g a ≤ potentialExpectation g b
  rw [potentialExpectation_remove_pair J.continuous hC a i j,
    potentialExpectation_remove_pair J.continuous hC b i j, hres, hb0, hb1]
  exact K.pair_comparison_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hc hsq
    (by linarith) (finiteAverage_norm_le hC r)

theorem weight_pair_comparison {n : ℕ} {R : ℝ} {g : ℝ → ℝ} (J : EvenJet R g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hR : Real.sqrt n < R)
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) (i j : Fin n) (hij : i ≠ j) :
    weightExpectation g w ≤ weightExpectation g (balanceWeights w i j) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    cases n with
    | zero => exact False.elim (hij ((Fin.eq_zero i).trans (Fin.eq_zero j).symm))
    | succ n =>
      obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hij.symm
      exact J.weight_pair_succ hC hR w hw i j'

theorem weight_expectation_le_flat {n : ℕ} (hn : 0 < n) {R : ℝ} {g : ℝ → ℝ}
    (J : EvenJet R g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hR : Real.sqrt n < R)
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) :
    weightExpectation g w ≤ weightExpectation g (flatWeights n) :=
  expectation_le_flat_of_pair_balancing hn J.continuous hC
    (J.weight_pair_comparison hC hR) w hw

/-- Global comparison for every signed coefficient vector, including zeros.
The test function is globally bounded but its analytic jet is needed only
on an interval containing the support of all normalized projections. -/
theorem expectation_le_diagonal {n : ℕ} (hn : 0 < n) {R : ℝ} {g : ℝ → ℝ}
    (J : EvenJet R g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hR : Real.sqrt n < R)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    potentialExpectation g a ≤ potentialExpectation g (diagonal n) := by
  have hw : (fun i => (a i) ^ 2) ∈ weightSimplex n :=
    ⟨fun i => sq_nonneg (a i), ha⟩
  have h := J.weight_expectation_le_flat hn hC hR _ hw
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
end
end ENT.Comparison
