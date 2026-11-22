module

public import ENT.Certificate.LogDerivative

/-! Third logarithmic derivative under an affine change of variable.
All claims are local at a point where the polynomial is nonzero. -/

@[expose] public section

set_option autoImplicit false

open scoped Topology
open Polynomial Filter

namespace ENT.Certificate

noncomputable section

def affineLogPotential (p : Polynomial ℝ) (a b x : ℝ) : ℝ :=
  -Real.log (p.eval (a * x + b))

theorem affineLogPotential_hasDerivAt (p : Polynomial ℝ) (a b x : ℝ)
    (hp : p.eval (a * x + b) ≠ 0) :
    HasDerivAt (affineLogPotential p a b)
      (-a * polynomialLogFirst p (a * x + b)) x := by
  have ha : HasDerivAt (fun y : ℝ => a * y + b) a x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul a).add_const b
  have hpoly := (p.hasDerivAt (a * x + b)).comp x ha
  have h := (hpoly.log hp).neg
  convert h using 1
  · rfl
  · simp only [polynomialLogFirst, Function.comp_apply]
    ring

theorem deriv_affineLogPotential (p : Polynomial ℝ) (a b x : ℝ)
    (hp : p.eval (a * x + b) ≠ 0) :
    deriv (affineLogPotential p a b) x =
      -a * polynomialLogFirst p (a * x + b) :=
  (affineLogPotential_hasDerivAt p a b x hp).deriv

theorem second_deriv_affineLogPotential (p : Polynomial ℝ) (a b x : ℝ)
    (hp : p.eval (a * x + b) ≠ 0) :
    deriv (deriv (affineLogPotential p a b)) x =
      -(a ^ 2) * polynomialLogSecond p (a * x + b) := by
  have hne : ∀ᶠ y in 𝓝 x, p.eval (a * y + b) ≠ 0 :=
    (p.differentiable.continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).continuousAt.eventually_ne hp
  have heq : deriv (affineLogPotential p a b) =ᶠ[𝓝 x]
      (fun y => -a * polynomialLogFirst p (a * y + b)) :=
    hne.mono (fun y hy => deriv_affineLogPotential p a b y hy)
  rw [heq.deriv_eq]
  have ha : HasDerivAt (fun y : ℝ => a * y + b) a x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul a).add_const b
  have h := ((polynomialLogFirst_hasDerivAt p (a * x + b) hp).comp x ha).const_mul (-a)
  convert h.deriv using 1 <;> first | rfl | ring

theorem third_deriv_affineLogPotential (p : Polynomial ℝ) (a b x : ℝ)
    (hp : p.eval (a * x + b) ≠ 0) :
    deriv (deriv (deriv (affineLogPotential p a b))) x =
      -(a ^ 3) * ((logarithmicNumeratorPolynomial p).eval (a * x + b) /
        (p.eval (a * x + b)) ^ 3) := by
  have hne : ∀ᶠ y in 𝓝 x, p.eval (a * y + b) ≠ 0 :=
    (p.differentiable.continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).continuousAt.eventually_ne hp
  have heq : deriv (deriv (affineLogPotential p a b)) =ᶠ[𝓝 x]
      (fun y => -(a ^ 2) * polynomialLogSecond p (a * y + b)) :=
    hne.mono (fun y hy => second_deriv_affineLogPotential p a b y hy)
  rw [heq.deriv_eq]
  have ha : HasDerivAt (fun y : ℝ => a * y + b) a x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul a).add_const b
  have h := ((polynomialLogSecond_hasDerivAt p (a * x + b) hp).comp x ha).const_mul (-(a ^ 2))
  convert h.deriv using 1 <;> first | rfl | ring

end
end ENT.Certificate
