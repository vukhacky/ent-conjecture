module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Algebra of pairwise balancing of squared coefficients. -/

set_option autoImplicit false
open scoped BigOperators

namespace ENT.Comparison

noncomputable section

/-- Replace two coordinates by their arithmetic mean. -/
def balanceWeights {n : ℕ} (w : Fin n → ℝ) (i j : Fin n) : Fin n → ℝ :=
  fun k => if k = i then (w i + w j) / 2
    else if k = j then (w i + w j) / 2 else w k

/-- Squared distance from a constant weight vector. -/
def weightEnergy {n : ℕ} (w : Fin n → ℝ) (c : ℝ) : ℝ :=
  ∑ k, (w k - c) ^ 2

theorem weightEnergy_nonneg {n : ℕ} (w : Fin n → ℝ) (c : ℝ) :
    0 ≤ weightEnergy w c :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem balanceWeights_nonneg {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hw : ∀ k, 0 ≤ w k) : ∀ k, 0 ≤ balanceWeights w i j k := by
  intro k
  simp only [balanceWeights]
  split_ifs
  · exact div_nonneg (add_nonneg (hw i) (hw j)) (by norm_num)
  · exact div_nonneg (add_nonneg (hw i) (hw j)) (by norm_num)
  · exact hw k

/-- Exact finite-sum substitution, useful for moments and deficit identities. -/
theorem sum_apply_balanceWeights {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (f : ℝ → ℝ) :
    (∑ k, f (balanceWeights w i j k)) =
      (∑ k, f (w k)) - f (w i) - f (w j) +
        2 * f ((w i + w j) / 2) := by
  have hpoint (k : Fin n) :
      f (balanceWeights w i j k) = f (w k) +
        (if k = i then f ((w i + w j) / 2) - f (w i) else 0) +
        (if k = j then f ((w i + w j) / 2) - f (w j) else 0) := by
    by_cases hi : k = i
    · subst k
      simp [balanceWeights, hij]
    · by_cases hj : k = j
      · subst k
        simp [balanceWeights, hi]
      · simp [balanceWeights, hi, hj]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib]
  simp
  ring

theorem sum_balanceWeights {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) :
    (∑ k, balanceWeights w i j k) = ∑ k, w k := by
  have h := sum_apply_balanceWeights w i j hij id
  dsimp at h
  linarith

/-- Averaging drops squared distance by exactly half the squared separation. -/
theorem weightEnergy_balanceWeights {n : ℕ} (w : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (c : ℝ) :
    weightEnergy (balanceWeights w i j) c =
      weightEnergy w c - (w i - w j) ^ 2 / 2 := by
  unfold weightEnergy
  rw [sum_apply_balanceWeights w i j hij (fun x => (x - c) ^ 2)]
  ring

theorem weightEnergy_balanceWeights_le {n : ℕ} (w : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (c : ℝ) :
    weightEnergy (balanceWeights w i j) c ≤ weightEnergy w c := by
  rw [weightEnergy_balanceWeights w i j hij c]
  nlinarith [sq_nonneg (w i - w j)]

/-- Range control of the energy; the center may be any point of the range. -/
theorem weightEnergy_le_card_mul_range_sq {n : ℕ} (w : Fin n → ℝ)
    (L U c : ℝ) (hw : ∀ k, L ≤ w k ∧ w k ≤ U)
    (hc : L ≤ c ∧ c ≤ U) :
    weightEnergy w c ≤ (n : ℝ) * (U - L) ^ 2 := by
  calc
    weightEnergy w c ≤ ∑ _k : Fin n, (U - L) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      have hleft : 0 ≤ (U - L) - (w k - c) := by linarith [(hw k).2, hc.1]
      have hright : 0 ≤ (U - L) + (w k - c) := by linarith [(hw k).1, hc.2]
      nlinarith [mul_nonneg hleft hright]
    _ = (n : ℝ) * (U - L) ^ 2 := by simp

theorem reciprocal_mem_weight_range {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℝ) (hsum : (∑ k, w k) = 1)
    (L U : ℝ) (hw : ∀ k, L ≤ w k ∧ w k ≤ U) :
    L ≤ (n : ℝ)⁻¹ ∧ (n : ℝ)⁻¹ ≤ U := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : (∑ _k : Fin n, L) ≤ ∑ k, w k :=
    Finset.sum_le_sum (fun k _ => (hw k).1)
  have hu : (∑ k, w k) ≤ ∑ _k : Fin n, U :=
    Finset.sum_le_sum (fun k _ => (hw k).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hsum] at hl hu
  constructor
  · have h : L ≤ 1 / (n : ℝ) :=
      (le_div_iff₀ hnR).2 (by simpa [mul_comm] using hl)
    simpa only [one_div] using h
  · have h : 1 / (n : ℝ) ≤ U :=
      (div_le_iff₀ hnR).2 (by simpa [mul_comm] using hu)
    simpa only [one_div] using h

/-- Quantitative contraction when a maximal and a minimal weight are balanced. -/
theorem weightEnergy_balance_extremes {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℝ) (hsum : (∑ k, w k) = 1)
    (i j : Fin n) (hij : i ≠ j)
    (hw : ∀ k, w j ≤ w k ∧ w k ≤ w i) :
    weightEnergy (balanceWeights w i j) (n : ℝ)⁻¹ ≤
      (1 - 1 / (2 * (n : ℝ))) * weightEnergy w (n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcenter := reciprocal_mem_weight_range hn w hsum (w j) (w i) hw
  have hbound := weightEnergy_le_card_mul_range_sq w (w j) (w i) (n : ℝ)⁻¹ hw hcenter
  have hstep : weightEnergy w (n : ℝ)⁻¹ / (2 * (n : ℝ)) ≤
      (w i - w j) ^ 2 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))).2
    nlinarith
  calc
    weightEnergy (balanceWeights w i j) (n : ℝ)⁻¹ =
        weightEnergy w (n : ℝ)⁻¹ - (w i - w j) ^ 2 / 2 :=
      weightEnergy_balanceWeights w i j hij _
    _ ≤ weightEnergy w (n : ℝ)⁻¹ -
        weightEnergy w (n : ℝ)⁻¹ / (2 * (n : ℝ)) := sub_le_sub_left hstep _
    _ = (1 - 1 / (2 * (n : ℝ))) * weightEnergy w (n : ℝ)⁻¹ := by ring

theorem geometric_energy_bound (e : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hstep : ∀ m, e (m + 1) ≤ r * e m) :
    ∀ m, e m ≤ r ^ m * e 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        e (m + 1) ≤ r * e m := hstep m
        _ ≤ r * (r ^ m * e 0) := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (m + 1) * e 0 := by rw [pow_succ]; ring

end
end ENT.Comparison
