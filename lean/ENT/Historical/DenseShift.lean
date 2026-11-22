module

public import ENT.Certificate.CanonicalPolynomials
public import ENT.Certificate.BlockSoundness

/-! Translation of dense integer polynomials and the corresponding coefficient formula. -/

@[expose] public section
set_option autoImplicit false
open Polynomial

namespace ENT.Certificate.Dense

/-- Translation by the integer `a`, in ascending coefficient order. -/
def shift (a : ℤ) : IntPoly → IntPoly
  | [] => []
  | b :: p => add [b] (mul [a, 1] (shift a p))

theorem eval_shift (a : ℤ) (p : IntPoly) (x : ℝ) :
    eval (shift a p) x = eval p (x + a) := by
  induction p with
  | nil => simp [shift]
  | cons b p ih =>
      simp only [shift, eval_add, eval_mul, eval_cons, eval_nil, Int.cast_one,
        mul_zero, add_zero, mul_one, ih]
      ring

theorem poly_add (p q : IntPoly) : Block.poly (add p q) = Block.poly p + Block.poly q := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
      cases q with
      | nil => simp [add]
      | cons b q => simp only [add, Block.poly_cons, ih, map_add]; ring

theorem poly_scale (a : ℤ) (p : IntPoly) :
    Block.poly (scale a p) = C a * Block.poly p := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
      simp only [scale, List.map_cons, Block.poly_cons, map_mul] at *
      rw [ih]
      ring

theorem poly_mul (p q : IntPoly) : Block.poly (mul p q) = Block.poly p * Block.poly q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
      simp only [mul, poly_add, poly_scale, Block.poly_cons, map_zero, zero_add, ih]
      ring

theorem poly_power (p : IntPoly) (n : ℕ) : Block.poly (power p n) = Block.poly p ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, poly_mul, ih, pow_succ, mul_comm]

theorem poly_derivative (p : IntPoly) :
    Block.poly (derivative p) = (Block.poly p).derivative := by
  induction p with
  | nil => simp [derivative]
  | cons a p ih =>
      cases p with
      | nil => simp [derivative]
      | cons b p =>
          simp only [derivative, poly_add, Block.poly_cons, map_zero, zero_add,
            Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
            Polynomial.derivative_X, one_mul, zero_add] at *
          rw [← ih]

theorem poly_shift (a : ℤ) (p : IntPoly) :
    Block.poly (shift a p) = (Block.poly p).comp (X + C a) := by
  induction p with
  | nil => simp [shift]
  | cons b p ih =>
      simp only [shift, poly_add, poly_mul, Block.poly_cons, Block.poly_nil,
        mul_zero, add_zero, map_one, mul_one, ih, add_comp, C_comp, mul_comp, X_comp]
      ring

end ENT.Certificate.Dense
