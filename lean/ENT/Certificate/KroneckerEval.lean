module

public import ENT.Certificate.KroneckerCore
public import ENT.Certificate.BlockPolynomial
public import ENT.Certificate.BernsteinCoefficients

/-! Exact polynomial semantics of packed integer evaluators. -/

@[expose] public section
set_option autoImplicit false
open Polynomial
open scoped BigOperators

namespace ENT.Certificate.Kronecker

noncomputable section

theorem intEval_eq (x : ℤ) (p : Pure.IntPoly) :
    intEval x p = (Block.poly p).eval x := by
  induction p with
  | nil => simp [intEval]
  | cons a p ih => simp only [intEval, Block.poly_cons, eval_add, eval_C, eval_mul, eval_X, ih]

theorem intEval_add (x : ℤ) (p q : Pure.IntPoly) :
    intEval x (Pure.Dense.add p q) = intEval x p + intEval x q := by
  simp only [intEval_eq, Block.poly_add, eval_add]

theorem intEval_scale (x a : ℤ) (p : Pure.IntPoly) :
    intEval x (Pure.Dense.scale a p) = a * intEval x p := by
  simp only [intEval_eq, Block.poly_scale, eval_mul, eval_C]

theorem intEval_mul (x : ℤ) (p q : Pure.IntPoly) :
    intEval x (Pure.Dense.mul p q) = intEval x p * intEval x q := by
  simp only [intEval_eq, Block.poly_mul, eval_mul]

theorem intEval_power (x : ℤ) (p : Pure.IntPoly) (n : ℕ) :
    intEval x (Pure.Dense.power p n) = intEval x p ^ n := by
  simp only [intEval_eq, Block.poly_power, eval_pow]

theorem intEval_curvature (n k : ℕ) (p : Pure.IntPoly) (x : ℤ) :
    intEval x (Pure.curvatureCoeffs n k p) = curvatureEval n k p x := by
  simp only [Pure.curvatureCoeffs, Pure.logarithmicNumeratorCoeffs,
    intEval_add, intEval_scale, intEval_mul, intEval_power, curvatureEval,
    intEval, mul_zero, add_zero]
  ring

def homogeneousPoly : List ℤ → Polynomial ℤ
  | [] => 0
  | b :: bs => C b * (1 - X)^bs.length + X * homogeneousPoly bs

theorem bernsteinEvalPair_fst (x : ℤ) (bs : List ℤ) :
    (bernsteinEvalPair x bs).1 = (1 - x)^bs.length := by
  induction bs with
  | nil => simp [bernsteinEvalPair]
  | cons b bs ih => simp only [bernsteinEvalPair, List.length_cons, ih, pow_succ]; ring

theorem bernsteinEvalPair_snd (x : ℤ) (bs : List ℤ) :
    (bernsteinEvalPair x bs).2 = (homogeneousPoly bs).eval x := by
  induction bs with
  | nil => simp [bernsteinEvalPair, homogeneousPoly]
  | cons b bs ih =>
      simp only [bernsteinEvalPair, homogeneousPoly, eval_add, eval_mul, eval_C,
        eval_pow, eval_sub, eval_one, eval_X, bernsteinEvalPair_fst, ih]

theorem homogeneousPoly_eq_sum (bs : List ℤ) :
    homogeneousPoly bs = ∑ j ∈ Finset.range bs.length,
      C (bs[j]?.getD 0) * X^j * (1 - X)^(bs.length - 1 - j) := by
  induction bs with
  | nil => simp [homogeneousPoly]
  | cons b bs ih =>
      rw [homogeneousPoly, ih, List.length_cons, Finset.sum_range_succ']
      simp only [Nat.add_sub_cancel, List.getElem?_cons_zero, Option.getD_some,
        pow_zero, mul_one, Nat.sub_zero, List.getElem?_cons_succ]
      rw [add_comm, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have he : bs.length - (j + 1) = bs.length - 1 - j := by omega
      rw [he, pow_succ]
      ring

theorem homogeneousPoly_eq_bernsteinPolynomial (D : ℕ) (bs : List ℤ)
    (hlen : bs.length = D + 1) :
    homogeneousPoly bs = BlockBernstein.bernsteinPolynomial D bs := by
  rw [homogeneousPoly_eq_sum, hlen]
  simp only [Nat.add_sub_cancel, BlockBernstein.bernsteinPolynomial]

theorem bernsteinEvalPair_eq (x : ℤ) (D : ℕ) (bs : List ℤ)
    (hlen : bs.length = D + 1) :
    (bernsteinEvalPair x bs).2 =
      (BlockBernstein.bernsteinPolynomial D bs).eval x := by
  rw [bernsteinEvalPair_snd, homogeneousPoly_eq_bernsteinPolynomial D bs hlen]

end
end ENT.Certificate.Kronecker
