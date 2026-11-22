module

public import ENT.Small.Quadrature
public import Mathlib.Data.Rat.Cast.Order

/-! Integer arithmetic for the degree-nine exponential Taylor polynomial. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory

namespace ENT.Small.Quadrature

open Certificate

def evalRat (p : IntPoly) (x : ℚ) : ℚ :=
  p.foldr (fun a acc => (a : ℚ) + x * acc) 0

def expTaylorInt10 (D : ℤ) (p : IntPoly) : IntPoly :=
  let q0 := [1]
  let q1 := Dense.add [9 * D] (Dense.mul p q0)
  let q2 := Dense.add [72 * D ^ 2] (Dense.mul p q1)
  let q3 := Dense.add [504 * D ^ 3] (Dense.mul p q2)
  let q4 := Dense.add [3024 * D ^ 4] (Dense.mul p q3)
  let q5 := Dense.add [15120 * D ^ 5] (Dense.mul p q4)
  let q6 := Dense.add [60480 * D ^ 6] (Dense.mul p q5)
  let q7 := Dense.add [181440 * D ^ 7] (Dense.mul p q6)
  let q8 := Dense.add [362880 * D ^ 8] (Dense.mul p q7)
  Dense.add [362880 * D ^ 9] (Dense.mul p q8)

noncomputable section

theorem evalRat_cast (p : IntPoly) (x : ℚ) : (evalRat p x : ℝ) = eval p (x : ℝ) := by
  induction p with
  | nil => simp [evalRat, eval]
  | cons a p ih =>
    change (((a : ℚ) + x * evalRat p x : ℚ) : ℝ) =
      (a : ℝ) + (x : ℝ) * eval p (x : ℝ)
    push_cast
    rw [ih]

theorem eval_expTaylorInt10 (D : ℤ) (hD : D ≠ 0) (p : IntPoly) (x : ℝ) :
    eval (expTaylorInt10 D p) x / (362880 * (D : ℝ) ^ 9) =
      Enclosures.expTaylor 10 (eval p x / (D : ℝ)) := by
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  unfold expTaylorInt10
  simp only [Dense.eval_add, Dense.eval_mul, Dense.eval_cons, Dense.eval_nil,
    mul_zero, add_zero, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  norm_num [Enclosures.expTaylor, Finset.sum_range_succ, Nat.factorial]
  field_simp [hDR]
  <;> ring

theorem expTaylor10_integral_eq {W : ℝ → ℝ} {p q F : IntPoly} {D M : ℤ}
    (hD : D ≠ 0) (hM : M ≠ 0) {c : ℝ}
    (harg : ∀ x : ℝ, eval p x / (D : ℝ) = c - W x)
    (hQ : q = expTaylorInt10 D p)
    (hF : Dense.derivative F = Dense.scale M q) (a b : ℚ) :
    (∫ x in (a : ℝ)..(b : ℝ), Enclosures.expTaylor 10 (c - W x)) =
      (((evalRat F b - evalRat F a) / (M : ℚ) /
        (362880 * (D : ℚ) ^ 9) : ℚ) : ℝ) := by
  have he : (fun x : ℝ => Enclosures.expTaylor 10 (c - W x)) =
      (fun x => eval q x / (362880 * (D : ℝ) ^ 9)) := by
    funext x
    rw [hQ, eval_expTaylorInt10 D hD, harg]
  rw [he, intervalIntegral.integral_div,
    integral_dense_of_primitive hM hF]
  push_cast
  rw [evalRat_cast, evalRat_cast]

end
end ENT.Small.Quadrature
