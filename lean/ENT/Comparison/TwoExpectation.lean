module

public import ENT.Comparison.TwoConvexOrder
public import ENT.Comparison.DensityExpectations
public import Mathlib.Topology.Order.LeftRightNhds

/-! Two-variable expectation comparison, including vanishing coefficients by continuity along a circle of fixed squared norm. -/

@[expose] public section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace ENT.Comparison
noncomputable section

theorem even_apply_abs {g : ℝ → ℝ} (heven : ∀ x, g (-x) = g x) (x : ℝ) :
    g |x| = g x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, heven]

theorem two_expectation_balancing_positive {a b c : ℝ} (hb : 0 < b) (hab : b < a)
    (hc : 0 < c) (hsq : 2 * c ^ 2 = a ^ 2 + b ^ 2)
    {g : ℝ → ℝ} (hg : Continuous g) (heven : ∀ x, g (-x) = g x)
    (hconv : ConvexOn ℝ (Icc 0 ((2 * c) ^ 2)) (fun x => g (Real.sqrt x))) :
    potentialExpectation g ![a, b] ≤ potentialExpectation g ![c, c] := by
  rw [potentialExpectation_twoDensity (hb.trans hab) hb hg,
    potentialExpectation_twoDensity hc hc hg]
  have h := twoDensity_convex_square_le hb hab hc hsq
    (hg.comp Real.continuous_sqrt).continuousOn hconv
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, even_apply_abs heven] using h

theorem two_expectation_balancing_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hsq : 2 * c ^ 2 = a ^ 2)
    {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (heven : ∀ x, g (-x) = g x)
    (hconv : ConvexOn ℝ (Icc 0 ((2 * c) ^ 2)) (fun x => g (Real.sqrt x))) :
    potentialExpectation g ![a, 0] ≤ potentialExpectation g ![c, c] := by
  have hcoeff : Continuous (fun ε : ℝ => (![Real.sqrt (a ^ 2 - ε ^ 2), ε] : Fin 2 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hcont := (continuous_potentialExpectation hg hC).comp hcoeff
  have hlim : Tendsto (fun ε : ℝ => potentialExpectation g ![Real.sqrt (a ^ 2 - ε ^ 2), ε])
      (𝓝[>] 0) (𝓝 (potentialExpectation g ![a, 0])) := by
    have h := hcont.continuousAt.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Function.comp_def, zero_pow (by decide : 2 ≠ 0), sub_zero,
      Real.sqrt_sq ha.le] using h
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (by positivity : 0 < a / 2)] with ε hε
  have harg : 0 < a ^ 2 - ε ^ 2 := by nlinarith [hε.1, hε.2]
  have hroot := Real.sq_sqrt harg.le
  have hεroot : ε < Real.sqrt (a ^ 2 - ε ^ 2) := by
    nlinarith [hε.1, hε.2, Real.sqrt_nonneg (a ^ 2 - ε ^ 2)]
  exact two_expectation_balancing_positive hε.1 hεroot hc (by nlinarith) hg heven hconv

theorem two_expectation_balancing {a b c : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hc : 0 < c) (hsq : 2 * c ^ 2 = a ^ 2 + b ^ 2)
    {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (heven : ∀ x, g (-x) = g x)
    (hconv : ConvexOn ℝ (Icc 0 ((2 * c) ^ 2)) (fun x => g (Real.sqrt x))) :
    potentialExpectation g ![a, b] ≤ potentialExpectation g ![c, c] := by
  have ha : 0 < a := by nlinarith
  rcases eq_or_lt_of_le hab with hab | hab
  · have hca : c = a := by nlinarith
    subst b
    subst c
    exact le_rfl
  rcases eq_or_lt_of_le hb with hb | hb
  · subst b
    exact two_expectation_balancing_zero ha hc (by simpa using hsq) hg hC heven hconv
  · exact two_expectation_balancing_positive hb hab hc hsq hg heven hconv

end
end ENT.Comparison
