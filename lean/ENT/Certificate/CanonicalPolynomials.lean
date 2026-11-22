module

public import ENT.Certificate.DenseDerivative

/-! Canonical integer computation of the spline and curvature target.
Its evaluation is tied to the analytic contract for every n and k. -/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace ENT.Certificate

def splineCoeffsAux (n k : ℕ) : ℕ → IntPoly
  | 0 => []
  | m + 1 => Dense.add (splineCoeffsAux n k m)
      (Dense.scale ((-1 : ℤ) ^ m * (Nat.fast_choose n m : ℤ))
        (Dense.power [(k : ℤ) - (m : ℤ), 1] (n - 1)))

def splineCoeffs (n k : ℕ) : IntPoly := splineCoeffsAux n k (k + 1)

theorem splineCoeffsAux_eval (n k m : ℕ) (x : ℝ) :
    eval (splineCoeffsAux n k m) x =
      ∑ j ∈ Finset.range m,
        (-1 : ℝ) ^ j * (n.choose j : ℝ) * ((k : ℝ) + x - (j : ℝ)) ^ (n - 1) := by
  induction m with
  | zero => simp [splineCoeffsAux]
  | succ m ih =>
      rw [splineCoeffsAux, Dense.eval_add, ih, Finset.sum_range_succ]
      congr 1
      rw [← Nat.choose_eq_fast_choose]
      simp only [Dense.eval_scale, Dense.eval_power, Dense.eval_cons,
        Dense.eval_nil, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, Int.cast_sub, mul_zero, add_zero, mul_one]
      congr 2
      ring

theorem splineCoeffs_eval (n k : ℕ) (x : ℝ) :
    eval (splineCoeffs n k) x = splinePiece n k x :=
  splineCoeffsAux_eval n k (k + 1) x

def logarithmicNumeratorCoeffs (p : IntPoly) : IntPoly :=
  Dense.add
    (Dense.add
      (Dense.mul (Dense.power p 2) (Dense.derivative (Dense.derivative (Dense.derivative p))))
      (Dense.scale (-3)
        (Dense.mul (Dense.mul p (Dense.derivative p)) (Dense.derivative (Dense.derivative p)))))
    (Dense.scale 2 (Dense.power (Dense.derivative p) 3))

theorem logarithmicNumeratorCoeffs_eval (p : IntPoly) (x : ℝ) :
    eval (logarithmicNumeratorCoeffs p) x = thirdLogNumerator (eval p) x := by
  simp only [logarithmicNumeratorCoeffs, Dense.eval_add, Dense.eval_mul,
    Dense.eval_scale, Dense.eval_power, thirdLogNumerator, Dense.deriv_eval]
  norm_num
  ring

def curvatureCoeffs (n k : ℕ) (p : IntPoly) : IntPoly :=
  Dense.add (Dense.scale ((n : ℤ) ^ 3) (logarithmicNumeratorCoeffs p))
    (Dense.scale (-56)
      (Dense.mul [(n : ℤ) - 2 * (k : ℤ), -2] (Dense.power p 3)))

theorem curvatureCoeffs_eval (n k : ℕ) (p : IntPoly)
    (hp : ∀ x : ℝ, eval p x = splinePiece n k x) (x : ℝ) :
    eval (curvatureCoeffs n k p) x = targetPolynomial n k x := by
  have hfun : eval p = splinePiece n k := funext hp
  simp only [curvatureCoeffs, Dense.eval_add, Dense.eval_scale, Dense.eval_mul,
    Dense.eval_power, logarithmicNumeratorCoeffs_eval, hfun, targetPolynomial,
    Dense.eval_cons, Dense.eval_nil]
  norm_num
  ring

end ENT.Certificate
