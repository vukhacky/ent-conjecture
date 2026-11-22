module

public import ENT.Certificate.DensePolynomial
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! A transparent dense derivative and its real analytic semantics. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Certificate.Dense

def derivative : IntPoly → IntPoly
  | [] => []
  | [_] => []
  | _ :: b :: p => add (b :: p) (0 :: derivative (b :: p))

theorem hasDerivAt_eval (p : IntPoly) (x : ℝ) :
    HasDerivAt (eval p) (eval (derivative p) x) x := by
  induction p with
  | nil =>
      convert hasDerivAt_const x (0 : ℝ) using 1 <;> rfl
  | cons a p ih =>
      cases p with
      | nil =>
          convert hasDerivAt_const x (a : ℝ) using 1
          · funext y
            simp
          · rfl
      | cons b p =>
          have h := ((hasDerivAt_id x).mul ih).const_add (a : ℝ)
          convert h using 1
          · rfl
          · simp only [derivative, eval_add, eval_cons, Int.cast_zero, zero_add,
              one_mul, id_eq]

theorem deriv_eval (p : IntPoly) : deriv (eval p) = eval (derivative p) := by
  funext x
  exact (hasDerivAt_eval p x).deriv

end ENT.Certificate.Dense
