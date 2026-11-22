module

public import ENT.Certificate.KroneckerSplineCore

/-! Direct curvature-to-Bernstein certificates. Each cell stores spline coefficients and Bernstein numerators. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace ENT.Certificate.KroneckerDirect

structure CellData where
  n : Nat
  k : Nat
  degreeBound : Nat
  halfCell : Bool
  pCoeffs : KroneckerLite.IntPoly
  bernsteinNumerators : List Int

def rCoeffBound (c : CellData) : Nat :=
  KroneckerLite.curvatureCoeffBound c.n c.k c.pCoeffs.length
    (KroneckerLite.sumAbs c.pCoeffs)

def qCoeffBound (c : CellData) : Nat :=
  if c.halfCell then 2 ^ c.degreeBound * rCoeffBound c else rCoeffBound c

def evaluationBase (c : CellData) (u : Int) : Int :=
  if c.halfCell then 2 * u else u

def transformScale (c : CellData) : Int :=
  if c.halfCell then 2 ^ c.degreeBound else 1

structure Valid (c : CellData) (pBase u : Int) : Prop where
  n_lower : 7 ≤ c.n
  n_upper : c.n ≤ 149
  cell : 2 * c.k < c.n
  half : c.halfCell = true ↔ 2 * c.k + 1 = c.n
  degree : c.degreeBound = 3 * c.n - 2
  p_length : c.pCoeffs.length = c.n
  p_bound : KroneckerLite.sumAbs c.pCoeffs +
    KroneckerSpline.canonicalCoeffBound c.n c.k < pBase.natAbs
  p_eval : KroneckerLite.intEval pBase c.pCoeffs =
    KroneckerSpline.canonicalEval c.n c.k pBase
  b_length : c.bernsteinNumerators.length = c.degreeBound + 1
  b_bound : (c.degreeBound + 1) * qCoeffBound c +
    KroneckerLite.bernsteinCoeffBound c.degreeBound c.bernsteinNumerators <
      (evaluationBase c u).natAbs
  direct_eval : (KroneckerLite.bernsteinEvalPair (evaluationBase c u)
      c.bernsteinNumerators).2 =
    transformScale c * KroneckerLite.curvatureEval c.n c.k c.pCoeffs u
  nonneg : c.bernsteinNumerators.all (fun b => decide (0 ≤ b)) = true

end ENT.Certificate.KroneckerDirect
