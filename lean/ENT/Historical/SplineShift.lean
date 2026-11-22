module

public import ENT.Historical.DenseShift
public import ENT.Certificate.PolynomialSemantics
public import Mathlib.Algebra.Polynomial.Roots

/-! Shift recurrence for the canonical spline cells and its dense integer coefficient formula. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace ENT.Certificate
noncomputable section

theorem splinePiece_shift_recurrence (n k : ℕ) (s : ℝ) :
    splinePiece n (k + 1) s = splinePiece n k (s + 1) +
      (-1 : ℝ) ^ (k + 1) * (n.choose (k + 1) : ℝ) * s ^ (n - 1) := by
  unfold splinePiece
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    congr 2
    push_cast
    ring
  · congr 1
    congr 1
    push_cast
    ring

theorem splinePolynomial_shift_recurrence (n k : ℕ) :
    splinePolynomial n (k + 1) = (splinePolynomial n k).comp (X + 1) +
      C ((-1 : ℝ) ^ (k + 1) * (n.choose (k + 1) : ℝ)) * X ^ (n - 1) := by
  apply Polynomial.funext
  intro x
  simpa only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    splinePolynomial_eval] using splinePiece_shift_recurrence n k x

def shiftedCellCoeffs (n k : ℕ) : IntPoly :=
  Dense.add (Dense.shift 1 (splineCoeffs n k))
    (Dense.scale ((-1 : ℤ) ^ (k + 1) * (Nat.fast_choose n (k + 1) : ℤ))
      (Dense.power [0, 1] (n - 1)))

theorem shiftedCellCoeffs_eval (n k : ℕ) (x : ℝ) :
    eval (shiftedCellCoeffs n k) x = splinePiece n (k + 1) x := by
  rw [shiftedCellCoeffs, Dense.eval_add, Dense.eval_shift, Dense.eval_scale,
    Dense.eval_power, splineCoeffs_eval, ← Nat.choose_eq_fast_choose]
  simp only [Dense.eval_cons, Dense.eval_nil, Int.cast_one, Int.cast_zero,
    mul_zero, add_zero, mul_one, zero_add, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_natCast]
  exact (splinePiece_shift_recurrence n k x).symm

theorem shiftedCellCoeffs_eq_canonical (n k : ℕ) :
    Block.poly (shiftedCellCoeffs n k) = Block.poly (splineCoeffs n (k + 1)) := by
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_map, Block.eval₂_poly,
    shiftedCellCoeffs_eval, splineCoeffs_eval]

end
end ENT.Certificate
