module

public import ENT.Certificate.KroneckerLiteCore

/-! Checks the spline coefficients by comparing polynomial values at an integer base. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace ENT.Certificate.KroneckerSpline

abbrev CellData := KroneckerLite.CellData

def canonicalCoeffBound (n k : Nat) : Nat :=
  (k + 1) * 2 ^ n * 2 ^ (n - 1) * (k + 1) ^ (n - 1)

def canonicalEvalAux (n k : Nat) (base : Int) : Nat → Int
  | 0 => 0
  | j + 1 => canonicalEvalAux n k base j +
      (-1 : Int) ^ j * (KroneckerLite.fastChoose n j : Int) *
        (base + (k : Int) - (j : Int)) ^ (n - 1)

def canonicalEval (n k : Nat) (base : Int) : Int :=
  canonicalEvalAux n k base (k + 1)

structure Valid (c : CellData) (pBase rBase bBase : Int) : Prop where
  n_lower : 7 ≤ c.n
  n_upper : c.n ≤ 149
  cell : 2 * c.k < c.n
  half : c.halfCell = true ↔ 2 * c.k + 1 = c.n
  degree : c.degreeBound ≤ 3 * c.n - 2
  r_length : c.rCoeffs.length ≤ c.degreeBound + 1
  p_length : c.pCoeffs.length = c.n
  p_bound : KroneckerLite.sumAbs c.pCoeffs + canonicalCoeffBound c.n c.k < pBase.natAbs
  p_eval : KroneckerLite.intEval pBase c.pCoeffs = canonicalEval c.n c.k pBase
  r_bound : KroneckerLite.sumAbs c.rCoeffs +
    KroneckerLite.curvatureCoeffBound c.n c.k c.pCoeffs.length
      (KroneckerLite.sumAbs c.pCoeffs) < rBase.natAbs
  r_eval : KroneckerLite.intEval rBase c.rCoeffs =
    KroneckerLite.curvatureEval c.n c.k c.pCoeffs rBase
  transform : c.transformedCoeffs =
    if c.halfCell then KroneckerLite.halfTransform c.degreeBound c.rCoeffs else c.rCoeffs
  b_length : c.bernsteinNumerators.length = c.degreeBound + 1
  b_bound : KroneckerLite.sumAbs c.transformedCoeffs +
    KroneckerLite.bernsteinCoeffBound c.degreeBound c.bernsteinNumerators < bBase.natAbs
  b_eval : KroneckerLite.intEval bBase c.transformedCoeffs =
    (KroneckerLite.bernsteinEvalPair bBase c.bernsteinNumerators).2
  nonneg : c.bernsteinNumerators.all (fun b => decide (0 ≤ b)) = true

end ENT.Certificate.KroneckerSpline
