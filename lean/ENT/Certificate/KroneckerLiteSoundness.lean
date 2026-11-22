module

public import ENT.Certificate.KroneckerLiteCore
public import ENT.Certificate.KroneckerSoundness

/-! Equivalence of the integer checks and the packed certificate conditions, including the cell indices, coefficient bounds, polynomial identities and sign conditions. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Certificate.KroneckerLite
noncomputable section

def toPureCell (c : CellData) : Pure.CellData where
  n := c.n
  k := c.k
  degreeBound := c.degreeBound
  halfCell := c.halfCell
  pCoeffs := c.pCoeffs
  rCoeffs := c.rCoeffs
  transformedCoeffs := c.transformedCoeffs
  bernsteinNumerators := c.bernsteinNumerators

theorem factorial_eq (n : Nat) : factorial n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorial, Nat.factorial, ih]

theorem descFactorial_eq (n k : Nat) : descFactorial n k = Nat.descFactorial n k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [descFactorial, Nat.descFactorial, ih]

theorem fastChoose_eq (n k : Nat) : fastChoose n k = Nat.fast_choose n k := by
  simp only [fastChoose, Nat.fast_choose, descFactorial_eq, factorial_eq]

theorem dense_add_eq (p q : IntPoly) : Dense.add p q = Pure.Dense.add p q := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
      cases q with
      | nil => rfl
      | cons b q => simp only [Dense.add, Pure.Dense.add, ih]

theorem dense_scale_eq (a : Int) (p : IntPoly) :
    Dense.scale a p = Pure.Dense.scale a p := rfl

theorem dense_derivative_eq (p : IntPoly) :
    Dense.derivative p = Pure.Dense.derivative p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      cases p with
      | nil => rfl
      | cons b p =>
          simp only [Dense.derivative, Pure.Dense.derivative, dense_add_eq, ih]

theorem binomialPowerCoeffs_eq (a : Int) (m : Nat) :
    binomialPowerCoeffs a m = PureFast.binomialPowerCoeffs a m := by
  simp only [binomialPowerCoeffs, PureFast.binomialPowerCoeffs, fastChoose_eq]

theorem fastSplineCoeffsAux_eq (n k m : Nat) :
    fastSplineCoeffsAux n k m = PureFast.fastSplineCoeffsAux n k m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [fastSplineCoeffsAux, PureFast.fastSplineCoeffsAux,
        dense_add_eq, dense_scale_eq, binomialPowerCoeffs_eq, fastChoose_eq, ih]

theorem fastSplineCoeffs_eq (n k : Nat) :
    fastSplineCoeffs n k = PureFast.fastSplineCoeffs n k :=
  fastSplineCoeffsAux_eq n k (k + 1)

theorem halfTransform_eq (d : Nat) (p : IntPoly) :
    halfTransform d p = Pure.halfTransform d p := by
  induction p generalizing d with
  | nil => rfl
  | cons a p ih => simp only [halfTransform, Pure.halfTransform, ih]

theorem sumAbs_eq (p : List Int) : sumAbs p = Kronecker.sumAbs p := rfl

theorem tripleFactor_eq (d : Nat) : tripleFactor d = Kronecker.tripleFactor d := rfl

theorem curvatureCoeffBound_eq (n k d M : Nat) :
    curvatureCoeffBound n k d M = Kronecker.curvatureCoeffBound n k d M := rfl

theorem bernsteinCoeffBound_eq (D : Nat) (bs : List Int) :
    bernsteinCoeffBound D bs = Kronecker.bernsteinCoeffBound D bs := rfl

theorem intEval_eq (x : Int) (p : IntPoly) : intEval x p = Kronecker.intEval x p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [intEval, Kronecker.intEval, ih]

theorem bernsteinEvalPair_eq (x : Int) (bs : List Int) :
    bernsteinEvalPair x bs = Kronecker.bernsteinEvalPair x bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [bernsteinEvalPair, Kronecker.bernsteinEvalPair, ih]

theorem curvatureEval_eq (n k : Nat) (p : IntPoly) (x : Int) :
    curvatureEval n k p x = Kronecker.curvatureEval n k p x := by
  simp only [curvatureEval, Kronecker.curvatureEval, dense_derivative_eq, intEval_eq]

theorem valid_to_kronecker (c : CellData) (rBase bBase : Int)
    (h : Valid c rBase bBase) : Kronecker.Valid (toPureCell c) rBase bBase where
  n_lower := h.n_lower
  n_upper := h.n_upper
  cell := h.cell
  half := h.half
  degree := h.degree
  r_length := h.r_length
  spline := by simpa only [toPureCell, fastSplineCoeffs_eq] using h.spline
  r_bound := by
    simpa only [toPureCell, sumAbs_eq, curvatureCoeffBound_eq] using h.r_bound
  r_eval := by simpa only [toPureCell, intEval_eq, curvatureEval_eq] using h.r_eval
  transform := by
    cases hf : c.halfCell <;> simpa [toPureCell, hf, halfTransform_eq] using h.transform
  b_length := h.b_length
  b_bound := by
    simpa only [toPureCell, sumAbs_eq, bernsteinCoeffBound_eq] using h.b_bound
  b_eval := by simpa only [toPureCell, intEval_eq, bernsteinEvalPair_eq] using h.b_eval
  nonneg := h.nonneg

theorem valid_of_kronecker (c : CellData) (rBase bBase : Int)
    (h : Kronecker.Valid (toPureCell c) rBase bBase) : Valid c rBase bBase where
  n_lower := h.n_lower
  n_upper := h.n_upper
  cell := h.cell
  half := h.half
  degree := h.degree
  r_length := h.r_length
  spline := by simpa only [toPureCell, fastSplineCoeffs_eq] using h.spline
  r_bound := by
    simpa only [toPureCell, sumAbs_eq, curvatureCoeffBound_eq] using h.r_bound
  r_eval := by simpa only [toPureCell, intEval_eq, curvatureEval_eq] using h.r_eval
  transform := by
    cases hf : c.halfCell <;> simpa [toPureCell, hf, halfTransform_eq] using h.transform
  b_length := h.b_length
  b_bound := by
    simpa only [toPureCell, sumAbs_eq, bernsteinCoeffBound_eq] using h.b_bound
  b_eval := by simpa only [toPureCell, intEval_eq, bernsteinEvalPair_eq] using h.b_eval
  nonneg := h.nonneg

theorem valid_iff (c : CellData) (rBase bBase : Int) :
    Valid c rBase bBase ↔ Kronecker.Valid (toPureCell c) rBase bBase :=
  ⟨valid_to_kronecker c rBase bBase, valid_of_kronecker c rBase bBase⟩

theorem valid_sound (c : CellData) (rBase bBase : Int) (h : Valid c rBase bBase) :
    CellConclusion (Pure.toSemanticData (toPureCell c)) :=
  Kronecker.valid_sound (toPureCell c) rBase bBase (valid_to_kronecker c rBase bBase h)

/-- Adapt an exported cell witness without changing its dimension, cell index
or either evaluation base.  The existing complete-family interface can then be
used without any change to its semantic contract. -/
theorem exists_valid_to_pure {n k : Nat}
    (h : ∃ c : CellData, c.n = n ∧ c.k = k ∧
      ∃ rBase bBase : Int, Valid c rBase bBase) :
    ∃ c : Pure.CellData, c.n = n ∧ c.k = k ∧
      ∃ rBase bBase : Int, Kronecker.Valid c rBase bBase := by
  rcases h with ⟨c, hn, hk, rBase, bBase, hc⟩
  exact ⟨toPureCell c, hn, hk, rBase, bBase, valid_to_kronecker c rBase bBase hc⟩

set_option pp.all true

end
end ENT.Certificate.KroneckerLite
