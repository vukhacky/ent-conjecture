module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Certificate data and polynomial identities for a spline cell. See `HornerChecker` for the checker and `CellSoundness` for its soundness proof. -/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace ENT.Certificate

noncomputable section

/-- Dense coefficients in ascending order. JSON integers are exact. -/
abbrev IntPoly := List ℤ

def eval (p : IntPoly) (x : ℝ) : ℝ :=
  p.foldr (fun a acc => (a : ℝ) + x * acc) 0

structure CellData where
  n : ℕ
  k : ℕ
  degreeBound : ℕ
  halfCell : Bool
  pCoeffs : IntPoly
  rCoeffs : IntPoly
  transformedCoeffs : IntPoly
  bernsteinNumerators : List ℤ

noncomputable def width (c : CellData) : ℝ :=
  if c.halfCell then (1 / 2 : ℝ) else 1

/-- This ties `pCoeffs` to the actual spline formula, not to an opaque input. -/
noncomputable def splinePiece (n k : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ j * (n.choose j : ℝ) * ((k : ℝ) + s - (j : ℝ)) ^ (n - 1)

def thirdLogNumerator (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  (f s) ^ 2 * deriv (deriv (deriv f)) s
    - 3 * f s * deriv f s * deriv (deriv f) s
    + 2 * (deriv f s) ^ 3

noncomputable def targetPolynomial (n k : ℕ) (s : ℝ) : ℝ :=
  (n : ℝ) ^ 3 * thirdLogNumerator (splinePiece n k) s
    - 56 * ((n : ℝ) - 2 * (k : ℝ) - 2 * s) * (splinePiece n k s) ^ 3

/-- Desired semantic conclusion of a successful cell check. -/
def CellConclusion (c : CellData) : Prop :=
  7 ≤ c.n ∧ c.n ≤ 149 ∧ 2 * c.k < c.n ∧
  (c.halfCell = true ↔ 2 * c.k + 1 = c.n) ∧
  (∀ s : ℝ, eval c.pCoeffs s = splinePiece c.n c.k s) ∧
  (∀ s : ℝ, eval c.rCoeffs s = targetPolynomial c.n c.k s) ∧
  (∀ s : ℝ, 0 ≤ s → s ≤ width c → 0 ≤ targetPolynomial c.n c.k s)

def Sound (checkCell : CellData → Bool) : Prop :=
  ∀ c : CellData, checkCell c = true → CellConclusion c

end
end ENT.Certificate
