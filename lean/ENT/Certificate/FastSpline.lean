module

public import ENT.Certificate.CanonicalPolynomials
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Sum

/-! A direct binomial expansion of each affine spline summand. This avoids
repeated dense polynomial multiplication when constructing its coefficients.
The evaluation theorem proves the semantic identity independently of data. -/

@[expose] public section
set_option autoImplicit false

open scoped BigOperators

namespace ENT.Certificate

theorem eval_ofFn {n : ℕ} (f : Fin n → ℤ) (x : ℝ) :
    eval (List.ofFn f) x = ∑ i : Fin n, (f i : ℝ) * x ^ (i : ℕ) := by
  induction n with
  | zero => simp [eval]
  | succ n ih =>
      rw [List.ofFn_succ, Dense.eval_cons, Fin.sum_univ_succ, ih]
      simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

def binomialPowerCoeffs (a : ℤ) (m : ℕ) : IntPoly :=
  List.ofFn (fun i : Fin (m + 1) =>
    (Nat.fast_choose m (i : ℕ) : ℤ) * a ^ (m - (i : ℕ)))

theorem binomialPowerCoeffs_eval (a : ℤ) (m : ℕ) (x : ℝ) :
    eval (binomialPowerCoeffs a m) x = ((a : ℝ) + x) ^ m := by
  rw [binomialPowerCoeffs, eval_ofFn, add_comm (a : ℝ) x, add_pow,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, ← Nat.choose_eq_fast_choose]
  ring

def fastSplineCoeffsAux (n k : ℕ) : ℕ → IntPoly
  | 0 => []
  | m + 1 => Dense.add (fastSplineCoeffsAux n k m)
      (Dense.scale ((-1 : ℤ) ^ m * (Nat.fast_choose n m : ℤ))
        (binomialPowerCoeffs ((k : ℤ) - (m : ℤ)) (n - 1)))

def fastSplineCoeffs (n k : ℕ) : IntPoly := fastSplineCoeffsAux n k (k + 1)

theorem fastSplineCoeffsAux_eval (n k m : ℕ) (x : ℝ) :
    eval (fastSplineCoeffsAux n k m) x =
      ∑ j ∈ Finset.range m,
        (-1 : ℝ) ^ j * (n.choose j : ℝ) * ((k : ℝ) + x - (j : ℝ)) ^ (n - 1) := by
  induction m with
  | zero => simp [fastSplineCoeffsAux]
  | succ m ih =>
      rw [fastSplineCoeffsAux, Dense.eval_add, ih, Finset.sum_range_succ]
      congr 1
      rw [← Nat.choose_eq_fast_choose]
      simp only [Dense.eval_scale, binomialPowerCoeffs_eval,
        Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, Int.cast_sub]
      congr 2
      ring

theorem fastSplineCoeffs_eval (n k : ℕ) (x : ℝ) :
    eval (fastSplineCoeffs n k) x = splinePiece n k x :=
  fastSplineCoeffsAux_eval n k (k + 1) x

end ENT.Certificate
