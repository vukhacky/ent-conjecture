module

public import ENT.Certificate.PolynomialSemantics
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
Analytic bridge for the exact logarithmic-derivative numerator.
Every statement is local to a point where the polynomial does not vanish.
No derivative identity at a zero or a support endpoint is asserted.
-/

@[expose] public section

set_option autoImplicit false

open scoped Topology
open Polynomial Filter

namespace ENT.Certificate

noncomputable section

def polynomialLogFirst (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  p.derivative.eval x / p.eval x

def polynomialLogSecond (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  (p.derivative.derivative.eval x * p.eval x - (p.derivative.eval x) ^ 2) /
    (p.eval x) ^ 2

theorem deriv_log_polynomial (p : Polynomial ℝ) (x : ℝ) (hp : p.eval x ≠ 0) :
    deriv (fun y => Real.log (p.eval y)) x = polynomialLogFirst p x := by
  exact ((p.hasDerivAt x).log hp).deriv

theorem polynomialLogFirst_hasDerivAt (p : Polynomial ℝ) (x : ℝ)
    (hp : p.eval x ≠ 0) :
    HasDerivAt (polynomialLogFirst p) (polynomialLogSecond p x) x := by
  convert (p.derivative.hasDerivAt x).div (p.hasDerivAt x) hp using 1
  · rfl
  · simp only [polynomialLogSecond, pow_two]

theorem polynomialLogSecond_hasDerivAt (p : Polynomial ℝ) (x : ℝ)
    (hp : p.eval x ≠ 0) :
    HasDerivAt (polynomialLogSecond p)
      ((logarithmicNumeratorPolynomial p).eval x / (p.eval x) ^ 3) x := by
  have hnum := ((p.derivative.derivative.hasDerivAt x).mul (p.hasDerivAt x)).sub
    ((p.derivative.hasDerivAt x).pow 2)
  have hden := (p.hasDerivAt x).pow 2
  convert hnum.div hden (pow_ne_zero 2 hp) using 1
  · rfl
  · simp only [logarithmicNumeratorPolynomial, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    field_simp [hp]
    <;> ring

theorem second_deriv_log_polynomial (p : Polynomial ℝ) (x : ℝ)
    (hp : p.eval x ≠ 0) :
    deriv (deriv (fun y => Real.log (p.eval y))) x = polynomialLogSecond p x := by
  have hne : ∀ᶠ y in 𝓝 x, p.eval y ≠ 0 :=
    p.differentiable.continuous.continuousAt.eventually_ne hp
  have heq : deriv (fun y => Real.log (p.eval y)) =ᶠ[𝓝 x]
      polynomialLogFirst p :=
    hne.mono (fun y hy => deriv_log_polynomial p y hy)
  rw [heq.deriv_eq]
  exact (polynomialLogFirst_hasDerivAt p x hp).deriv

theorem third_deriv_log_polynomial (p : Polynomial ℝ) (x : ℝ)
    (hp : p.eval x ≠ 0) :
    deriv (deriv (deriv (fun y => Real.log (p.eval y)))) x =
      (logarithmicNumeratorPolynomial p).eval x / (p.eval x) ^ 3 := by
  have hne : ∀ᶠ y in 𝓝 x, p.eval y ≠ 0 :=
    p.differentiable.continuous.continuousAt.eventually_ne hp
  have heq : deriv (deriv (fun y => Real.log (p.eval y))) =ᶠ[𝓝 x]
      polynomialLogSecond p :=
    hne.mono (fun y hy => second_deriv_log_polynomial p y hy)
  rw [heq.deriv_eq]
  exact (polynomialLogSecond_hasDerivAt p x hp).deriv

end
end ENT.Certificate
