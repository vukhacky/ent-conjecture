module

public import ENT.Small.TaylorFourth
public import ENT.Small.LocalGeometry
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Taylor's quadratic expansion with a measurable third-derivative envelope,
followed by integration with all integrability premises explicit. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology

namespace ENT.Small
noncomputable section

def taylorTwo (F : ℝ → ℝ) (r x : ℝ) : ℝ :=
  F r + deriv F r * (x - r) + iteratedDeriv 2 F r * (x - r) ^ 2 / 2

theorem taylorTwo_eq_taylorWithin {F : ℝ → ℝ} {r x : ℝ} (hne : r ≠ x)
    (hF : ContDiffAt ℝ 2 F r) :
    taylorTwo F r x = taylorWithinEval F 2 (uIcc r x) r x := by
  have hu := uniqueDiffOn_uIcc hne
  have hjet (k : ℕ) (hk : k ≤ 2) :
      iteratedDerivWithin k F (uIcc r x) r = iteratedDeriv k F r :=
    iteratedDerivWithin_eq_iteratedDeriv hu (hF.of_le (by exact_mod_cast hk)) left_mem_uIcc
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, hjet 1 (by decide),
    hjet 2 (by decide), iteratedDeriv_one, smul_eq_mul]
  norm_num [taylorTwo, Nat.factorial]
  ring

theorem taylorTwo_remainder_bound {F : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hF : ContDiffOn ℝ 2 F s) {r x M : ℝ} (hsub : uIcc r x ⊆ s)
    (hd : ∀ y ∈ uIoo r x, ∃ v : ℝ,
      HasDerivAt (iteratedDeriv 2 F) v y ∧ |v| ≤ M) :
    |F x - taylorTwo F r x| ≤ M * |x - r| ^ 3 / 6 := by
  by_cases hne : r = x
  · subst x
    simp [taylorTwo]
  have hu := uniqueDiffOn_uIcc hne
  have hclosed (y : ℝ) (hy : y ∈ uIcc r x) : ContDiffAt ℝ 2 F y :=
    hF.contDiffAt (hs.mem_nhds (hsub hy))
  have heq (y : ℝ) (hy : y ∈ uIoo r x) :
      iteratedDerivWithin 2 F (uIcc r x) =ᶠ[𝓝 y] iteratedDeriv 2 F := by
    filter_upwards [Icc_mem_nhds hy.1 hy.2] with z hz
    exact iteratedDerivWithin_eq_iteratedDeriv hu (hclosed z hz) hz
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin 2 F (uIcc r x)) (uIoo r x) := by
    intro y hy
    obtain ⟨v, hv, _⟩ := hd y hy
    exact (hv.congr_of_eventuallyEq (heq y hy)).differentiableAt.differentiableWithinAt
  obtain ⟨y, hy, hrem⟩ := taylor_mean_remainder_lagrange hne (hF.mono hsub) hdiff
  obtain ⟨v, hv, hbound⟩ := hd y hy
  have hv' := hv.congr_of_eventuallyEq (heq y hy)
  have hj : iteratedDerivWithin 3 F (uIcc r x) y = v := by
    rw [iteratedDerivWithin_succ]
    exact hv'.hasDerivWithinAt.derivWithin (hu y ⟨hy.1.le, hy.2.le⟩)
  rw [hj] at hrem
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one] at hrem
  rw [taylorTwo_eq_taylorWithin hne (hclosed r left_mem_uIcc), hrem,
    abs_div, abs_mul, abs_pow]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbound (pow_nonneg (abs_nonneg _) 3)) (by norm_num)

theorem taylorTwo_increment_upper {F : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hF : ContDiffOn ℝ 2 F s) {r y M : ℝ} (hsub : uIcc r (r + y) ⊆ s)
    (hd : ∀ x ∈ uIoo r (r + y), ∃ v : ℝ,
      HasDerivAt (iteratedDeriv 2 F) v x ∧ |v| ≤ M) :
    F (r + y) - F r ≤ deriv F r * y + iteratedDeriv 2 F r * y ^ 2 / 2 + M * |y| ^ 3 / 6 := by
  have h := (abs_le.mp (taylorTwo_remainder_bound hs hF hsub hd)).2
  simp only [taylorTwo, add_sub_cancel_left] at h
  linarith

theorem integral_taylorTwo_increment_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y H : Ω → ℝ) (F : ℝ → ℝ) {s : Set ℝ}
    (hs : IsOpen s) (hF : ContDiffOn ℝ 2 F s)
    (hsub : ∀ᵐ ω ∂μ, uIcc (X ω) (X ω + Y ω) ⊆ s)
    (hd : ∀ᵐ ω ∂μ, ∀ x ∈ uIoo (X ω) (X ω + Y ω), ∃ v : ℝ,
      HasDerivAt (iteratedDeriv 2 F) v x ∧ |v| ≤ H ω)
    (hinc : Integrable (fun ω => F (X ω + Y ω) - F (X ω)) μ)
    (hlin : Integrable (fun ω => deriv F (X ω) * Y ω) μ)
    (hquad : Integrable (fun ω => iteratedDeriv 2 F (X ω) * Y ω ^ 2) μ)
    (hrem : Integrable (fun ω => H ω * |Y ω| ^ 3) μ) :
    (∫ ω, F (X ω + Y ω) - F (X ω) ∂μ) ≤
      (∫ ω, deriv F (X ω) * Y ω ∂μ) +
        (∫ ω, iteratedDeriv 2 F (X ω) * Y ω ^ 2 ∂μ) / 2 +
          (∫ ω, H ω * |Y ω| ^ 3 ∂μ) / 6 := by
  have hpoint : ∀ᵐ ω ∂μ, F (X ω + Y ω) - F (X ω) ≤
      deriv F (X ω) * Y ω + iteratedDeriv 2 F (X ω) * Y ω ^ 2 / 2 + H ω * |Y ω| ^ 3 / 6 := by
    filter_upwards [hsub, hd] with ω hω hdω
    exact taylorTwo_increment_upper hs hF hω hdω
  have h := integral_mono_ae hinc ((hlin.fun_add (hquad.div_const 2)).fun_add (hrem.div_const 6)) hpoint
  rwa [integral_add (hlin.fun_add (hquad.div_const 2)) (hrem.div_const 6),
    integral_add hlin (hquad.div_const 2), integral_div, integral_div] at h

end
end ENT.Small
