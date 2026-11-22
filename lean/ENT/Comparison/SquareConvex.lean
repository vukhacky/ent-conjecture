module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
The scalar analytic input for the two-coefficient comparison: a function whose
derivative is convex and vanishes at zero becomes convex after composition
with square root. The zero endpoint is covered by continuity, not by an
invalid derivative of square root at zero.
-/

@[expose] public section
set_option autoImplicit false
open Set

namespace ENT.Comparison
noncomputable section

theorem sqrt_mem_Icc_square {R x : ℝ} (hR : 0 ≤ R) (hx : x ∈ Icc 0 (R ^ 2)) :
    Real.sqrt x ∈ Icc 0 R := by
  refine ⟨Real.sqrt_nonneg x, ?_⟩
  have hsq := Real.sq_sqrt hx.1
  nlinarith [Real.sqrt_nonneg x, hx.2]

theorem sqrt_mem_Ioo_square {R x : ℝ} (hR : 0 < R) (hx : x ∈ Ioo 0 (R ^ 2)) :
    Real.sqrt x ∈ Ioo 0 R := by
  refine ⟨Real.sqrt_pos.mpr hx.1, ?_⟩
  have hsq := Real.sq_sqrt hx.1.le
  nlinarith [Real.sqrt_nonneg x, hx.2]

theorem convex_sqrt_comp_of_convex_derivative {g g' : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hg : ContinuousOn g (Icc 0 R))
    (hderiv : ∀ x ∈ Ioo 0 R, HasDerivAt g (g' x) x)
    (hg' : ConvexOn ℝ (Icc 0 R) g') (hg'zero : g' 0 = 0) :
    ConvexOn ℝ (Icc 0 (R ^ 2)) (fun x => g (Real.sqrt x)) := by
  have hcont : ContinuousOn (fun x => g (Real.sqrt x)) (Icc 0 (R ^ 2)) :=
    hg.comp Real.continuous_sqrt.continuousOn (fun _ hx => sqrt_mem_Icc_square hR.le hx)
  have hd : ∀ x ∈ Ioo 0 (R ^ 2),
      HasDerivAt (fun x => g (Real.sqrt x)) (g' (Real.sqrt x) / (2 * Real.sqrt x)) x := by
    intro x hx
    simpa only [Function.comp_def, div_eq_mul_inv, one_mul] using
      (hderiv _ (sqrt_mem_Ioo_square hR hx)).comp x (Real.hasDerivAt_sqrt hx.1.ne')
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 (R ^ 2)) hcont
  · rw [interior_Icc]
    intro x hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    rw [(hd x hx).deriv, (hd y hy).deriv]
    have hsx := sqrt_mem_Ioo_square hR hx
    have hsy := sqrt_mem_Ioo_square hR hy
    have hslope := hg'.secant_mono ⟨le_rfl, hR.le⟩
      ⟨hsx.1.le, hsx.2.le⟩ ⟨hsy.1.le, hsy.2.le⟩ hsx.1.ne' hsy.1.ne'
      (Real.sqrt_le_sqrt hxy)
    simp only [hg'zero, sub_zero] at hslope
    have hdiv := div_le_div_of_nonneg_right hslope (by norm_num : (0 : ℝ) ≤ 2)
    convert hdiv using 1 <;> ring

theorem convex_sqrt_comp_of_third_derivative {g g' g'' g''' : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hg : ContinuousOn g (Icc 0 R))
    (hg' : ContinuousOn g' (Icc 0 R)) (hg'zero : g' 0 = 0)
    (hd1 : ∀ x ∈ Ioo 0 R, HasDerivAt g (g' x) x)
    (hd2 : ∀ x ∈ Ioo 0 R, HasDerivAt g' (g'' x) x)
    (hd3 : ∀ x ∈ Ioo 0 R, HasDerivAt g'' (g''' x) x)
    (hnonneg : ∀ x ∈ Ioo 0 R, 0 ≤ g''' x) :
    ConvexOn ℝ (Icc 0 (R ^ 2)) (fun x => g (Real.sqrt x)) := by
  apply convex_sqrt_comp_of_convex_derivative hR hg hd1 _ hg'zero
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 R) hg'
  · intro x hx
    exact (hd2 x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
  · intro x hx
    exact (hd3 x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
  · simpa only [interior_Icc] using hnonneg

end
end ENT.Comparison
