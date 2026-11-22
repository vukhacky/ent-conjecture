module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Fourth-order Taylor remainder with a fifth derivative bound only in the
open segment. This allows the expansion point to be a spline knot. -/

@[expose] public section

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace ENT.Small

noncomputable section

def taylorFour (F : ℝ → ℝ) (r x : ℝ) : ℝ :=
  F r + deriv F r * (x - r) + iteratedDeriv 2 F r * (x - r) ^ 2 / 2 +
    iteratedDeriv 3 F r * (x - r) ^ 3 / 6 + iteratedDeriv 4 F r * (x - r) ^ 4 / 24

theorem taylorFour_eq_taylorWithin {F : ℝ → ℝ} {r x : ℝ} (hne : r ≠ x)
    (hF : ContDiffAt ℝ 4 F r) :
    taylorFour F r x = taylorWithinEval F 4 (uIcc r x) r x := by
  have hu := uniqueDiffOn_uIcc hne
  have hjet (k : ℕ) (hk : k ≤ 4) :
      iteratedDerivWithin k F (uIcc r x) r = iteratedDeriv k F r :=
    iteratedDerivWithin_eq_iteratedDeriv hu (hF.of_le (by exact_mod_cast hk)) left_mem_uIcc
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, hjet 1 (by decide),
    hjet 2 (by decide), hjet 3 (by decide), hjet 4 (by decide), iteratedDeriv_one, smul_eq_mul]
  norm_num [taylorFour, Nat.factorial]
  ring

theorem taylorFour_remainder_bound {F : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hF : ContDiffOn ℝ 4 F s) {r x M : ℝ} (hsub : uIcc r x ⊆ s)
    (hd : ∀ y ∈ uIoo r x, ∃ v : ℝ,
      HasDerivAt (iteratedDeriv 4 F) v y ∧ |v| ≤ M) :
    |F x - taylorFour F r x| ≤ M * |x - r| ^ 5 / 120 := by
  by_cases hne : r = x
  · subst x
    simp [taylorFour]
  have hu := uniqueDiffOn_uIcc hne
  have hclosed (y : ℝ) (hy : y ∈ uIcc r x) : ContDiffAt ℝ 4 F y :=
    hF.contDiffAt (hs.mem_nhds (hsub hy))
  have heq (y : ℝ) (hy : y ∈ uIoo r x) :
      iteratedDerivWithin 4 F (uIcc r x) =ᶠ[𝓝 y] iteratedDeriv 4 F := by
    filter_upwards [Icc_mem_nhds hy.1 hy.2] with z hz
    exact iteratedDerivWithin_eq_iteratedDeriv hu (hclosed z hz) hz
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin 4 F (uIcc r x)) (uIoo r x) := by
    intro y hy
    obtain ⟨v, hv, _⟩ := hd y hy
    exact (hv.congr_of_eventuallyEq (heq y hy)).differentiableAt.differentiableWithinAt
  obtain ⟨y, hy, hrem⟩ := taylor_mean_remainder_lagrange hne (hF.mono hsub) hdiff
  obtain ⟨v, hv, hbound⟩ := hd y hy
  have hv' := hv.congr_of_eventuallyEq (heq y hy)
  have hj : iteratedDerivWithin 5 F (uIcc r x) y = v := by
    rw [iteratedDerivWithin_succ]
    exact hv'.hasDerivWithinAt.derivWithin (hu y ⟨hy.1.le, hy.2.le⟩)
  rw [hj] at hrem
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one] at hrem
  rw [taylorFour_eq_taylorWithin hne (hclosed r left_mem_uIcc), hrem,
    abs_div, abs_mul, abs_pow]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 120)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbound (pow_nonneg (abs_nonneg _) 5)) (by norm_num)

end
end ENT.Small
