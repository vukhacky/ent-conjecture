module

public import ENT.Certificate.PureFast
public import ENT.Certificate.KroneckerBoundCore

/-! Integer arithmetic for packed polynomial identity checks. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Certificate.Kronecker

def intEval (x : ℤ) : Pure.IntPoly → ℤ
  | [] => 0
  | a :: p => a + x * intEval x p

/-- Homogeneous Horner evaluation; first component is `(1-x)^length`.
For a nonempty list of length `D+1`, the second component is the Bernstein
polynomial of degree `D` evaluated at `x`. -/
def bernsteinEvalPair (x : ℤ) : List ℤ → ℤ × ℤ
  | [] => (1, 0)
  | b :: bs =>
      let prev := bernsteinEvalPair x bs
      ((1 - x) * prev.1, b * prev.1 + x * prev.2)

def curvatureEval (n k : ℕ) (p : Pure.IntPoly) (x : ℤ) : ℤ :=
  let d := Pure.Dense.derivative p
  let e := Pure.Dense.derivative d
  let f := Pure.Dense.derivative e
  let P := intEval x p
  let D := intEval x d
  let E := intEval x e
  let F := intEval x f
  (n : ℤ)^3 * (P^2 * F - 3 * P * D * E + 2 * D^3) -
    56 * ((n : ℤ) - 2 * (k : ℤ) - 2*x) * P^3

structure Valid (c : Pure.CellData) (rBase bBase : ℤ) : Prop where
  n_lower : 7 ≤ c.n
  n_upper : c.n ≤ 149
  cell : 2 * c.k < c.n
  half : c.halfCell = true ↔ 2 * c.k + 1 = c.n
  degree : c.degreeBound ≤ 3 * c.n - 2
  r_length : c.rCoeffs.length ≤ c.degreeBound + 1
  spline : c.pCoeffs = PureFast.fastSplineCoeffs c.n c.k
  r_bound : sumAbs c.rCoeffs +
    curvatureCoeffBound c.n c.k c.pCoeffs.length (sumAbs c.pCoeffs) < rBase.natAbs
  r_eval : intEval rBase c.rCoeffs = curvatureEval c.n c.k c.pCoeffs rBase
  transform : c.transformedCoeffs =
    if c.halfCell then Pure.halfTransform c.degreeBound c.rCoeffs else c.rCoeffs
  b_length : c.bernsteinNumerators.length = c.degreeBound + 1
  b_bound : sumAbs c.transformedCoeffs +
    bernsteinCoeffBound c.degreeBound c.bernsteinNumerators < bBase.natAbs
  b_eval : intEval bBase c.transformedCoeffs =
    (bernsteinEvalPair bBase c.bernsteinNumerators).2
  nonneg : c.bernsteinNumerators.all (fun b => decide (0 ≤ b)) = true

end ENT.Certificate.Kronecker
