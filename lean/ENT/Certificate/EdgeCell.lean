module

public import ENT.Certificate.PolynomialSemantics
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! A symbolic proof for every edge cell k=0. This avoids the large lists
of zeros created by generic dense arithmetic in high dimensions. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Certificate

noncomputable section

theorem splinePiece_edge (n : ℕ) (s : ℝ) : splinePiece n 0 s = s ^ (n - 1) := by
  simp [splinePiece]

theorem thirdLogNumerator_power (m : ℕ) (s : ℝ) :
    thirdLogNumerator (fun y : ℝ => y ^ (m + 3)) s =
      2 * ((m : ℝ) + 3) * (s ^ m) ^ 3 * s ^ 6 := by
  have he3 : m + 3 - 1 = m + 2 := by omega
  have he2 : m + 2 - 1 = m + 1 := by omega
  have he1 : m + 1 - 1 = m := by omega
  have h1 : deriv (fun y : ℝ => y ^ (m + 3)) =
      fun y => ((m : ℝ) + 3) * y ^ (m + 2) := by
    funext y
    convert ((hasDerivAt_id y).pow (m + 3)).deriv using 1
    · rfl
    · simp only [id_eq, mul_one, he3, Nat.cast_add, Nat.cast_ofNat]
  have h2 : deriv (fun y : ℝ => ((m : ℝ) + 3) * y ^ (m + 2)) =
      fun y => ((m : ℝ) + 3) * ((m : ℝ) + 2) * y ^ (m + 1) := by
    funext y
    convert (((hasDerivAt_id y).pow (m + 2)).const_mul ((m : ℝ) + 3)).deriv using 1
    · rfl
    · simp only [id_eq, mul_one, he2, Nat.cast_add, Nat.cast_ofNat]
      ring
  have h3 : deriv (fun y : ℝ => ((m : ℝ) + 3) * ((m : ℝ) + 2) * y ^ (m + 1)) =
      fun y => ((m : ℝ) + 3) * ((m : ℝ) + 2) * ((m : ℝ) + 1) * y ^ m := by
    funext y
    convert (((hasDerivAt_id y).pow (m + 1)).const_mul
      (((m : ℝ) + 3) * ((m : ℝ) + 2))).deriv using 1
    · rfl
    · simp only [id_eq, mul_one, he1, Nat.cast_add, Nat.cast_one]
      ring
  unfold thirdLogNumerator
  rw [h1, h2, h3]
  simp only [pow_add]
  ring

theorem targetPolynomial_edge_factor (m : ℕ) (s : ℝ) :
    targetPolynomial (m + 4) 0 s =
      2 * (s ^ m) ^ 3 * s ^ 6 *
        (((m : ℝ) + 4) ^ 3 * ((m : ℝ) + 3) -
          28 * ((m : ℝ) + 4 - 2 * s) * s ^ 3) := by
  have hf : splinePiece (m + 4) 0 = fun y : ℝ => y ^ (m + 3) := by
    funext y
    rw [splinePiece_edge]
    congr 1
  unfold targetPolynomial
  rw [hf, thirdLogNumerator_power]
  norm_num only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero]
  simp only [pow_add]
  ring

theorem targetPolynomial_edge_nonneg (n : ℕ) (hn : 4 ≤ n) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 ≤ targetPolynomial n 0 s := by
  let m := n - 4
  have hn' : n = m + 4 := by dsimp [m]; omega
  rw [hn', targetPolynomial_edge_factor]
  apply mul_nonneg (by positivity)
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hbase : 0 ≤ ((m : ℝ) + 4) ^ 3 * ((m : ℝ) + 3) - 28 * ((m : ℝ) + 4) := by
    ring_nf
    positivity
  have hprod : ((m : ℝ) + 4 - 2 * s) * s ^ 3 ≤ (m : ℝ) + 4 := by
    calc
      _ ≤ ((m : ℝ) + 4) * 1 := mul_le_mul (by linarith)
        (pow_le_one₀ hs0 hs1) (pow_nonneg hs0 3) (by positivity)
      _ = (m : ℝ) + 4 := mul_one _
  linarith

end
end ENT.Certificate
