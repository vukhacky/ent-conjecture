module

public import ENT.Pang.FourierTransfer
public import ENT.Pang.CurvatureAlgebra
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Actual logarithmic derivatives and the algebraic curvature expression. -/

@[expose] public section

set_option autoImplicit false

open Filter Set
open scoped Topology

attribute [local instance 1001] NormedField.toNormedSpace

namespace ENT.Pang

noncomputable section

def logSecondJet (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv (deriv f) x * f x - (deriv f x) ^ 2) / (f x) ^ 2

theorem logSecondJet_hasDerivAt {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hf1 : DifferentiableAt ℝ (deriv f) x)
    (hf2 : DifferentiableAt ℝ (deriv (deriv f)) x) (hfx : f x ≠ 0) :
    HasDerivAt (logSecondJet f)
      (logThirdExpression (f x) (deriv f x) (iteratedDeriv 2 f x) (iteratedDeriv 3 f x)) x := by
  have hnum := (hf2.hasDerivAt.mul hf.hasDerivAt).sub (hf1.hasDerivAt.pow 2)
  have hden := hf.hasDerivAt.pow 2
  convert hnum.div hden (pow_ne_zero 2 hfx) using 1
  · rfl
  · simp only [logThirdExpression, iteratedDeriv_succ, iteratedDeriv_zero,
      Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    field_simp [hfx]
    <;> ring

theorem second_deriv_log_eq_logSecondJet {f : ℝ → ℝ} {x : ℝ}
    (hf : Differentiable ℝ f) (hf1 : Differentiable ℝ (deriv f)) (hfx : f x ≠ 0) :
    deriv (deriv (fun y => Real.log (f y))) x = logSecondJet f x := by
  have hne : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.continuous.continuousAt.eventually_ne hfx
  have heq : deriv (fun y => Real.log (f y)) =ᶠ[𝓝 x] (fun y => deriv f y / f y) :=
    hne.mono fun y hy => deriv.log (hf y) hy
  rw [heq.deriv_eq]
  convert ((hf1 x).hasDerivAt.div (hf x).hasDerivAt hfx).deriv using 1
  simp only [logSecondJet, pow_two]

theorem third_deriv_log_eq_logThirdExpression {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiff ℝ 3 f) (hfx : f x ≠ 0) :
    iteratedDeriv 3 (fun y => Real.log (f y)) x =
      logThirdExpression (f x) (deriv f x) (iteratedDeriv 2 f x) (iteratedDeriv 3 f x) := by
  have hf1 : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hf2 : ContDiff ℝ 1 (deriv (deriv f)) := hf1.deriv'
  have hd := hf.differentiable (by norm_num)
  have hd1 := hf1.differentiable (by norm_num)
  have hd2 := hf2.differentiable (by norm_num)
  have hne : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.continuous.continuousAt.eventually_ne hfx
  have heq : deriv (deriv (fun y => Real.log (f y))) =ᶠ[𝓝 x] logSecondJet f :=
    hne.mono fun y hy => second_deriv_log_eq_logSecondJet hd hd1 hy
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [heq.deriv_eq]
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    (logSecondJet_hasDerivAt (hd x) (hd1 x) (hd2 x) hfx).deriv

theorem standardizedPotential_third_deriv_eq_neg_logThirdExpression {n : ℕ} (hn : 6 ≤ n)
    {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 3 (standardizedPotential n t) 0 =
      -logThirdExpression (standardizedDensity n t 0)
        (deriv (standardizedDensity n t) 0)
        (iteratedDeriv 2 (standardizedDensity n t) 0)
        (iteratedDeriv 3 (standardizedDensity n t) 0) := by
  unfold standardizedPotential
  rw [iteratedDeriv_fun_neg, third_deriv_log_eq_logThirdExpression
    (by simpa using contDiff_standardizedDensity ht (N := 3) (by omega))
    (standardizedDensity_zero_pos (by omega) ht).ne']

theorem diagonalPotential_third_deriv_pos_of_logThird {n : ℕ} (hn : 6 ≤ n)
    (h : ∀ t : ℝ, 0 < t →
      logThirdExpression (standardizedDensity n t 0)
        (deriv (standardizedDensity n t) 0)
        (iteratedDeriv 2 (standardizedDensity n t) 0)
        (iteratedDeriv 3 (standardizedDensity n t) 0) < 0) :
    ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt (n : ℝ)),
      0 < iteratedDeriv 3 (Spline.diagonalSplinePotential n) x := by
  apply diagonalPotential_third_deriv_pos_of_tilt (by omega)
  intro t ht
  rw [standardizedPotential_third_deriv_eq_neg_logThirdExpression hn ht]
  exact neg_pos.mpr (h t ht)

theorem diagonalPotential_third_deriv_pos_of_pang_bounds {n : ℕ} (hn : 150 ≤ n)
    (hfirst : ∀ t : ℝ, 0 < t → 0 < deriv (standardizedDensity n t) 0)
    (hbracket : ∀ t : ℝ, 0 < t →
      lowerDerivativeBracket (standardizedDensity n t 0)
        (deriv (standardizedDensity n t) 0)
        (iteratedDeriv 2 (standardizedDensity n t) 0) < 7 / 2)
    (hsign : ∀ t : ℝ, 0 < t →
      iteratedDeriv 3 (standardizedDensity n t) 0 +
        (7 / 2) * deriv (standardizedDensity n t) 0 < 0) :
    ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt (n : ℝ)),
      0 < deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x := by
  have h := diagonalPotential_third_deriv_pos_of_logThird (by omega : 6 ≤ n)
    (fun t ht => logThirdExpression_neg_of_pang_bounds
      (standardizedDensity_zero_pos (by omega) ht) (hfirst t ht) (hbracket t ht) (hsign t ht))
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h

end
end ENT.Pang
