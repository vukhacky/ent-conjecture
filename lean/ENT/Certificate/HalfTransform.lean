module

public import ENT.Certificate.DensePolynomial
public import Mathlib.Tactic.NormNum

/-! Exact integer half-cell transform with an explicit coefficient-length guard. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Certificate

def halfTransform (d : ℕ) : IntPoly → IntPoly
  | [] => []
  | a :: p => ((2 : ℤ) ^ d * a) :: halfTransform (d - 1) p

theorem halfTransform_eval (p : IntPoly) (d : ℕ)
    (hlen : p.length ≤ d + 1) (x : ℝ) :
    eval (halfTransform d p) x = (2 : ℝ) ^ d * eval p (x / 2) := by
  induction p generalizing d with
  | nil => simp [halfTransform]
  | cons a p ih =>
      cases d with
      | zero =>
          have hp : p = [] := by
            cases p with
            | nil => rfl
            | cons b q => simp only [List.length_cons] at hlen; omega
          simp [hp, halfTransform]
      | succ d =>
          have hp : p.length ≤ d + 1 := by simp only [List.length_cons] at hlen; omega
          simp only [halfTransform, Dense.eval_cons, Nat.add_sub_cancel, ih d hp,
            Int.cast_mul, Int.cast_pow, Int.cast_ofNat, pow_succ]
          ring

end ENT.Certificate
