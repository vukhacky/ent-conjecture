module

public import ENT.Certificate.Contract
public import Mathlib.Tactic.Ring

/-! Transparent integer polynomial arithmetic, with real evaluation soundness. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Certificate.Dense

def add : IntPoly → IntPoly → IntPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℤ) (p : IntPoly) : IntPoly := p.map (fun b => a * b)

def mul : IntPoly → IntPoly → IntPoly
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

def power (p : IntPoly) : ℕ → IntPoly
  | 0 => [1]
  | n + 1 => mul p (power p n)

@[simp] theorem eval_nil (x : ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (a : ℤ) (p : IntPoly) (x : ℝ) :
    eval (a :: p) x = (a : ℝ) + x * eval p x := rfl

theorem eval_add (p q : IntPoly) (x : ℝ) :
    eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
      cases q with
      | nil => simp [add]
      | cons b q =>
          simp only [add, eval_cons, ih, Int.cast_add]
          ring

theorem eval_scale (a : ℤ) (p : IntPoly) (x : ℝ) :
    eval (scale a p) x = (a : ℝ) * eval p x := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
      simp only [scale, List.map_cons, eval_cons, Int.cast_mul] at *
      rw [ih]
      ring

theorem eval_mul (p q : IntPoly) (x : ℝ) :
    eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
      simp only [mul, eval_add, eval_scale, eval_cons, Int.cast_zero, zero_add, ih]
      ring

theorem eval_power (p : IntPoly) (n : ℕ) (x : ℝ) :
    eval (power p n) x = eval p x ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
      rw [power, eval_mul, ih, pow_succ]
      ring

end ENT.Certificate.Dense
