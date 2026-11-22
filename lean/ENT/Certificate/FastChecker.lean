module

public import ENT.Certificate.FastSpline
public import ENT.Certificate.HalfTransform
public import ENT.Certificate.CellSoundness

/-! A cell checker that constructs the spline coefficients directly from the binomial formula. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Certificate

def FastCellArithmeticValid (c : CellData) : Prop :=
  7 ≤ c.n ∧ c.n ≤ 149 ∧ 2 * c.k < c.n ∧
    (c.halfCell = true ↔ 2 * c.k + 1 = c.n) ∧
    c.degreeBound ≤ 3 * c.n - 2 ∧
    c.rCoeffs.length ≤ c.degreeBound + 1 ∧
    c.pCoeffs = fastSplineCoeffs c.n c.k ∧
    c.rCoeffs = curvatureCoeffs c.n c.k c.pCoeffs ∧
    c.transformedCoeffs =
      if c.halfCell then halfTransform c.degreeBound c.rCoeffs else c.rCoeffs

instance (c : CellData) : Decidable (FastCellArithmeticValid c) := by
  unfold FastCellArithmeticValid
  infer_instance

def fastCheckCell (c : CellData) : Bool :=
  decide (FastCellArithmeticValid c) &&
    checkBernsteinHorner c.degreeBound c.transformedCoeffs c.bernsteinNumerators

theorem fastCheckCell_sound : Sound fastCheckCell := by
  intro c hc
  have hparts := Bool.and_eq_true_iff.mp hc
  have ha : FastCellArithmeticValid c := of_decide_eq_true hparts.1
  rcases ha with ⟨hn0, hn1, hk, hhalf, _hdegree, hlength, hp, hr, hq⟩
  have hpsem : ∀ x : ℝ, eval c.pCoeffs x = splinePiece c.n c.k x := by
    intro x
    rw [hp]
    exact fastSplineCoeffs_eval c.n c.k x
  have hrsem : ∀ x : ℝ, eval c.rCoeffs x = targetPolynomial c.n c.k x := by
    intro x
    rw [hr]
    exact curvatureCoeffs_eval c.n c.k c.pCoeffs hpsem x
  have ht : TransformIdentity c := by
    intro x
    rw [hq]
    cases hflag : c.halfCell with
    | false => simp only [hflag, Bool.false_eq_true, ↓reduceIte]
    | true =>
        simp only [hflag, ↓reduceIte]
        exact halfTransform_eval c.rCoeffs c.degreeBound hlength x
  exact cellConclusion_of_bernstein c hn0 hn1 hk hhalf hpsem hrsem ht hparts.2

end ENT.Certificate
