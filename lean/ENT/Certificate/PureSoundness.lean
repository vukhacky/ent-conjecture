module

public import ENT.Certificate.Pure
public import ENT.Certificate.CompleteChecker

/-! Kernel-checked semantic adapter for the import-light integer checker.
The executable checkers are proved equal by induction on their integer-list computations. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Certificate.Pure

def toSemanticData (c : CellData) : ENT.Certificate.CellData where
  n := c.n
  k := c.k
  degreeBound := c.degreeBound
  halfCell := c.halfCell
  pCoeffs := c.pCoeffs
  rCoeffs := c.rCoeffs
  transformedCoeffs := c.transformedCoeffs
  bernsteinNumerators := c.bernsteinNumerators

theorem dense_add_eq (p q : IntPoly) : Dense.add p q = ENT.Certificate.Dense.add p q := by
  induction p generalizing q with
  | nil => simp [Dense.add, ENT.Certificate.Dense.add]
  | cons a p ih =>
      cases q with
      | nil => simp [Dense.add, ENT.Certificate.Dense.add]
      | cons b q => simp [Dense.add, ENT.Certificate.Dense.add, ih]

theorem dense_scale_eq (a : ℤ) (p : IntPoly) : Dense.scale a p = ENT.Certificate.Dense.scale a p := rfl

theorem dense_mul_eq (p q : IntPoly) : Dense.mul p q = ENT.Certificate.Dense.mul p q := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [Dense.mul, ENT.Certificate.Dense.mul, dense_add_eq, dense_scale_eq, ih]

theorem dense_power_eq (p : IntPoly) (n : ℕ) : Dense.power p n = ENT.Certificate.Dense.power p n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Dense.power, ENT.Certificate.Dense.power, dense_mul_eq, ih]

theorem dense_derivative_eq (p : IntPoly) : Dense.derivative p = ENT.Certificate.Dense.derivative p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      cases p with
      | nil => rfl
      | cons b p => simp [Dense.derivative, ENT.Certificate.Dense.derivative, dense_add_eq, ih]

theorem splineAux_eq (n k m : ℕ) : splineCoeffsAux n k m = ENT.Certificate.splineCoeffsAux n k m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [splineCoeffsAux, ENT.Certificate.splineCoeffsAux, dense_add_eq, dense_scale_eq,
        dense_power_eq, ih]

theorem spline_eq (n k : ℕ) : splineCoeffs n k = ENT.Certificate.splineCoeffs n k :=
  splineAux_eq n k (k + 1)

theorem numerator_eq (p : IntPoly) :
    logarithmicNumeratorCoeffs p = ENT.Certificate.logarithmicNumeratorCoeffs p := by
  simp only [logarithmicNumeratorCoeffs, ENT.Certificate.logarithmicNumeratorCoeffs,
    dense_add_eq, dense_mul_eq, dense_scale_eq, dense_power_eq, dense_derivative_eq]

theorem curvature_eq (n k : ℕ) (p : IntPoly) :
    curvatureCoeffs n k p = ENT.Certificate.curvatureCoeffs n k p := by
  simp only [curvatureCoeffs, ENT.Certificate.curvatureCoeffs, numerator_eq,
    dense_add_eq, dense_mul_eq, dense_scale_eq, dense_power_eq]

theorem halfTransform_eq (d : ℕ) (p : IntPoly) :
    halfTransform d p = ENT.Certificate.halfTransform d p := by
  induction p generalizing d with
  | nil => rfl
  | cons a p ih => simp [halfTransform, ENT.Certificate.halfTransform, ih]

theorem bernsteinHorner_eq (bs : List ℤ) :
    bernsteinHorner bs = ENT.Certificate.bernsteinHorner bs := by
  induction bs with
  | nil => rfl
  | cons a bs ih =>
      cases bs with
      | nil => rfl
      | cons b bs =>
          simp only [bernsteinHorner, ENT.Certificate.bernsteinHorner, dense_add_eq,
            dense_mul_eq, dense_scale_eq, ih]

theorem bernsteinCheck_eq (d : ℕ) (p : IntPoly) (bs : List ℤ) :
    checkBernsteinHorner d p bs = ENT.Certificate.checkBernsteinHorner d p bs := by
  unfold checkBernsteinHorner ENT.Certificate.checkBernsteinHorner
  rw [bernsteinHorner_eq]

theorem arithmetic_iff (c : CellData) :
    CellArithmeticValid c ↔ ENT.Certificate.CellArithmeticValid (toSemanticData c) := by
  simp only [CellArithmeticValid, ENT.Certificate.CellArithmeticValid, toSemanticData,
    spline_eq, curvature_eq, halfTransform_eq]
  rfl

theorem checkCell_eq_semantic (c : CellData) :
    checkCell c = ENT.Certificate.checkCell (toSemanticData c) := by
  unfold checkCell ENT.Certificate.checkCell
  rw [bernsteinCheck_eq]
  congr 1
  exact decide_eq_decide.mpr (arithmetic_iff c)

theorem checkCell_sound (c : CellData) (hc : checkCell c = true) :
    ENT.Certificate.CellConclusion (toSemanticData c) := by
  apply ENT.Certificate.checkCell_sound
  rw [← checkCell_eq_semantic]
  exact hc

end ENT.Certificate.Pure
