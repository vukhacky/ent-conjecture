module

public import ENT.Small.TaylorFourth
public import Mathlib.Tactic.Linarith

/-! A one-sided quadratic Taylor upper bound valid at an integrable logarithmic endpoint. -/

@[expose] public section

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace ENT.Small

noncomputable section

theorem taylorSecond_upper_of_nonneg_third {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {x R : ℝ} (hx : x ≤ R)
    (hd : ∀ y ∈ Ioo x R, ∃ v : ℝ, HasDerivAt (iteratedDeriv 2 F) v y ∧ 0 ≤ v) :
    F x ≤ F R + deriv F R * (x - R) + iteratedDeriv 2 F R * (x - R) ^ 2 / 2 := by
  by_cases hxeq : x = R
  · subst x
    simp
  have hne : R ≠ x := Ne.symm hxeq
  have hlt : x < R := lt_of_le_of_ne hx hxeq
  have hu := uniqueDiffOn_uIcc hne
  have heq (y : ℝ) (hy : y ∈ uIoo R x) :
      iteratedDerivWithin 2 F (uIcc R x) =ᶠ[𝓝 y] iteratedDeriv 2 F := by
    filter_upwards [Icc_mem_nhds hy.1 hy.2] with z hz
    exact iteratedDerivWithin_eq_iteratedDeriv hu hF.contDiffAt hz
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin 2 F (uIcc R x)) (uIoo R x) := by
    intro y hy
    have hy' : y ∈ Ioo x R := by simpa only [uIoo, min_eq_right hx, max_eq_left hx] using hy
    obtain ⟨v, hv, _⟩ := hd y hy'
    exact (hv.congr_of_eventuallyEq (heq y hy)).differentiableAt.differentiableWithinAt
  obtain ⟨y, hy, hrem⟩ := taylor_mean_remainder_lagrange hne hF.contDiffOn hdiff
  have hy' : y ∈ Ioo x R := by simpa only [uIoo, min_eq_right hx, max_eq_left hx] using hy
  obtain ⟨v, hv, hv0⟩ := hd y hy'
  have hv' := hv.congr_of_eventuallyEq (heq y hy)
  have hj : iteratedDerivWithin 3 F (uIcc R x) y = v := by
    rw [iteratedDerivWithin_succ]
    exact hv'.hasDerivWithinAt.derivWithin (hu y ⟨hy.1.le, hy.2.le⟩)
  have hjet (k : ℕ) (hk : k ≤ 2) :
      iteratedDerivWithin k F (uIcc R x) R = iteratedDeriv k F R :=
    iteratedDerivWithin_eq_iteratedDeriv hu (hF.contDiffAt.of_le (by exact_mod_cast hk)) left_mem_uIcc
  have ht : taylorWithinEval F 2 (uIcc R x) R x =
      F R + deriv F R * (x - R) + iteratedDeriv 2 F R * (x - R) ^ 2 / 2 := by
    simp only [taylorWithinEval_succ, taylor_within_zero_eval, hjet 1 (by decide),
      hjet 2 (by decide), iteratedDeriv_one, smul_eq_mul]
    norm_num [Nat.factorial]
    ring
  rw [hj, ht] at hrem
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one] at hrem
  have hp : (x - R) ^ 3 ≤ 0 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sq_nonneg (x - R))]
  have hm := mul_nonpos_of_nonneg_of_nonpos hv0 hp
  linarith

end
end ENT.Small
