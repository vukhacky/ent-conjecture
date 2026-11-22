module

public import ENT.Pang.LargeNCurvature
public import ENT.Spline.Symmetry
public import ENT.Spline.SupportInterior
public import Mathlib.Analysis.Calculus.MeanValue

/-! A Gaussian envelope from nonnegative third potential curvature.
All logarithms are evaluated only where the density is strictly positive. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace ENT.Quantitative
noncomputable section

theorem potential_lower_quadratic_nonneg {R c : ℝ} (hR : 0<R) {V : ℝ→ℝ}
    (heven : Function.Even V)
    (hsmooth : ∀ x∈Ioo (-R) R, ContDiffAt ℝ 3 V x)
    (hcurv : ∀ x∈Ioo (0:ℝ) R, 0≤deriv (deriv (deriv V)) x)
    (hsecond : c≤deriv (deriv V) 0)
    {x : ℝ} (hx0 : 0≤x) (hxR : x<R) :
    V 0+c*x^2/2≤V x := by
  have hreg (z : ℝ) (hz : z∈Icc (0:ℝ) x) : ContDiffAt ℝ 3 V z :=
    hsmooth z ⟨by linarith [hz.1],hz.2.trans_lt hxR⟩
  have hd (z : ℝ) (hz : z∈Icc (0:ℝ) x) : DifferentiableAt ℝ V z :=
    (hreg z hz).differentiableAt (by norm_num)
  have hd1 (z : ℝ) (hz : z∈Icc (0:ℝ) x) : DifferentiableAt ℝ (deriv V) z := by
    have h1 : ContDiffAt ℝ 2 (deriv V) z := (hreg z hz).derivWithin (by norm_num)
    exact h1.differentiableAt (by norm_num)
  have hd2 (z : ℝ) (hz : z∈Icc (0:ℝ) x) : DifferentiableAt ℝ (deriv (deriv V)) z := by
    have h1 : ContDiffAt ℝ 2 (deriv V) z := (hreg z hz).derivWithin (by norm_num)
    have h2 : ContDiffAt ℝ 1 (deriv (deriv V)) z := h1.derivWithin (by norm_num)
    exact h2.differentiableAt (by norm_num)
  have hm2 : MonotoneOn (deriv (deriv V)) (Icc (0:ℝ) x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun z hz=>(hd2 z hz).continuousAt.continuousWithinAt
    · exact fun z hz=>(hd2 z (interior_subset hz)).differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact hcurv z ⟨hz.1,hz.2.trans hxR⟩
  have hsecondAll (z : ℝ) (hz : z∈Icc (0:ℝ) x) : c≤deriv (deriv V) z :=
    hsecond.trans (hm2 ⟨le_rfl,hx0⟩ hz hz.1)
  have hFder (z : ℝ) (hz : z∈Icc (0:ℝ) x) :
      HasDerivAt (fun y=>deriv V y-c*y) (deriv (deriv V) z-c) z := by
    convert (hd1 z hz).hasDerivAt.sub ((hasDerivAt_id z).const_mul c) using 1 <;> simp [Pi.sub_def]
  have hmF : MonotoneOn (fun y=>deriv V y-c*y) (Icc (0:ℝ) x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun z hz=>(hFder z hz).continuousAt.continuousWithinAt
    · exact fun z hz=>(hFder z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hFder z (interior_subset hz)).deriv]
      exact sub_nonneg.mpr (hsecondAll z (interior_subset hz))
  have hFnonneg (z : ℝ) (hz : z∈Icc (0:ℝ) x) : 0≤deriv V z-c*z := by
    have h := hmF ⟨le_rfl,hx0⟩ hz hz.1
    simpa only [Spline.deriv_zero_of_even V heven,mul_zero,sub_self] using h
  have hGder (z : ℝ) (hz : z∈Icc (0:ℝ) x) :
      HasDerivAt (fun y=>V y-c*y^2/2) (deriv V z-c*z) z := by
    convert (hd z hz).hasDerivAt.sub ((((hasDerivAt_id z).pow 2).const_mul c).div_const 2) using 1
    · rfl
    · simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,id_eq]
      ring
  have hmG : MonotoneOn (fun y=>V y-c*y^2/2) (Icc (0:ℝ) x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun z hz=>(hGder z hz).continuousAt.continuousWithinAt
    · exact fun z hz=>(hGder z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hGder z (interior_subset hz)).deriv]
      exact hFnonneg z (interior_subset hz)
  have h := hmG ⟨le_rfl,hx0⟩ ⟨hx0,le_rfl⟩ hx0
  norm_num only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_div,sub_zero] at h
  linarith

/-- An even potential with increasing curvature lies above its quadratic tangent. -/
theorem even_potential_lower_quadratic {R c : ℝ} (hR : 0<R) {V : ℝ→ℝ}
    (heven : Function.Even V)
    (hsmooth : ∀ x∈Ioo (-R) R, ContDiffAt ℝ 3 V x)
    (hcurv : ∀ x∈Ioo (0:ℝ) R, 0≤deriv (deriv (deriv V)) x)
    (hsecond : c≤deriv (deriv V) 0) :
    ∀ x∈Ioo (-R) R, V 0+c*x^2/2≤V x := by
  intro x hx
  by_cases hx0 : 0≤x
  · exact potential_lower_quadratic_nonneg hR heven hsmooth hcurv hsecond hx0 hx.2
  · have h := potential_lower_quadratic_nonneg hR heven hsmooth hcurv hsecond
      (x:= -x) (by linarith) (by linarith [hx.1])
    simpa only [neg_sq,heven x] using h

/-- Gaussian density envelope, including the support endpoints and exterior. -/
theorem density_le_gaussian_of_third_curvature {R c : ℝ} (hR : 0<R) {f : ℝ→ℝ}
    (heven : Function.Even f)
    (hpos : ∀ x∈Ioo (-R) R, 0<f x)
    (hzero : ∀ x, x∉Ioo (-R) R → f x=0)
    (hsmooth : ∀ x∈Ioo (-R) R, ContDiffAt ℝ 3 (fun y=>-Real.log (f y)) x)
    (hcurv : ∀ x∈Ioo (0:ℝ) R,
      0≤deriv (deriv (deriv (fun y=>-Real.log (f y)))) x)
    (hsecond : c≤deriv (deriv (fun y=>-Real.log (f y))) 0) :
    ∀ x : ℝ, f x≤f 0*Real.exp (-c*x^2/2) := by
  have hf0 : 0<f 0 := hpos 0 ⟨by linarith,hR⟩
  have hV_even : Function.Even (fun y=>-Real.log (f y)) := by
    intro y
    dsimp only
    rw [heven y]
  intro x
  by_cases hx : x∈Ioo (-R) R
  · have h := even_potential_lower_quadratic hR hV_even hsmooth hcurv hsecond x hx
    have hlog : Real.log (f x)≤Real.log (f 0)-c*x^2/2 := by linarith
    calc
      f x=Real.exp (Real.log (f x)) := (Real.exp_log (hpos x hx)).symm
      _≤Real.exp (Real.log (f 0)-c*x^2/2) := Real.exp_le_exp.mpr hlog
      _=f 0*Real.exp (-c*x^2/2) := by
        rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hf0]
        congr 2
        ring
  · rw [hzero x hx]
    exact (mul_pos hf0 (Real.exp_pos _)).le

/-- Application to the actual diagonal density; the sole extra numerical input
is the lower bound on the second potential derivative at the origin. -/
theorem diagonal_density_gaussian_envelope {n : ℕ} (hn : 150≤n) {c : ℝ}
    (hsecond : c≤deriv (deriv (Spline.diagonalSplinePotential n)) 0) :
    ∀ x : ℝ, Spline.diagonalSplineDensity n x≤
      Spline.diagonalSplineDensity n 0*Real.exp (-c*x^2/2) := by
  apply density_le_gaussian_of_third_curvature
    (show 0<Real.sqrt (n:ℝ) from Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega)))
    (Spline.diagonalSplineDensity_even n (by omega))
    (Spline.diagonalSplineDensity_pos n (by omega))
    (Spline.diagonalSplineDensity_eq_zero_of_not_mem_interior n (by omega))
  · intro x hx
    exact Spline.contDiffAt_diagonalSplinePotential 3 n (by omega) x
      (ne_of_gt (Spline.diagonalSplineDensity_pos n (by omega) x hx))
  · exact Pang.pang_large_n_curvature_nonneg hn
  · exact hsecond

end
end ENT.Quantitative
