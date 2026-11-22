module

public import ENT.Certificate.Contract
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic.Ring

/-!
The polynomial model of the spline and curvature target. The bridge theorems
tie certificate arithmetic to the derivative-based semantic contract.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace ENT.Certificate

noncomputable section

def splinePolynomial (n k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    C ((-1 : ℝ) ^ j * (n.choose j : ℝ)) *
      (C (k : ℝ) + X - C (j : ℝ)) ^ (n - 1)

theorem splinePolynomial_eval (n k : ℕ) (x : ℝ) :
    (splinePolynomial n k).eval x = splinePiece n k x := by
  simp [splinePolynomial, splinePiece, Polynomial.eval_finsetSum]

def logarithmicNumeratorPolynomial (p : Polynomial ℝ) : Polynomial ℝ :=
  p ^ 2 * p.derivative.derivative.derivative
    - 3 * p * p.derivative * p.derivative.derivative
    + 2 * p.derivative ^ 3

theorem logarithmicNumeratorPolynomial_eval (p : Polynomial ℝ) (x : ℝ) :
    (logarithmicNumeratorPolynomial p).eval x =
      thirdLogNumerator (fun y => p.eval y) x := by
  have h1 : deriv (fun y : ℝ => p.eval y) = fun y => p.derivative.eval y := by
    funext y
    exact p.deriv
  have h2 : deriv (fun y : ℝ => p.derivative.eval y) =
      fun y => p.derivative.derivative.eval y := by
    funext y
    exact p.derivative.deriv
  have h3 : deriv (fun y : ℝ => p.derivative.derivative.eval y) =
      fun y => p.derivative.derivative.derivative.eval y := by
    funext y
    exact p.derivative.derivative.deriv
  simp only [thirdLogNumerator, h1, h2, h3, logarithmicNumeratorPolynomial,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat]

def curvaturePolynomial (n k : ℕ) : Polynomial ℝ :=
  C ((n : ℝ) ^ 3) * logarithmicNumeratorPolynomial (splinePolynomial n k)
    - 56 * (C (n : ℝ) - 2 * C (k : ℝ) - 2 * X) *
      (splinePolynomial n k) ^ 3

theorem curvaturePolynomial_eval (n k : ℕ) (x : ℝ) :
    (curvaturePolynomial n k).eval x = targetPolynomial n k x := by
  have hfun : splinePiece n k = fun y => (splinePolynomial n k).eval y := by
    funext y
    exact (splinePolynomial_eval n k y).symm
  unfold curvaturePolynomial targetPolynomial
  rw [hfun]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_pow,
    logarithmicNumeratorPolynomial_eval]

end
end ENT.Certificate
