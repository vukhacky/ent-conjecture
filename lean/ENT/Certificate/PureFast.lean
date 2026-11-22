module

public import ENT.Certificate.Pure
public import Mathlib.Data.List.OfFn

/-! Import-light execution of the direct-binomial complete checker.
The semantic adapter is in PureFastSoundness, separately from computation. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Certificate.PureFast

open Pure

def binomialPowerCoeffs (a : ℤ) (m : ℕ) : Pure.IntPoly :=
  List.ofFn (fun i : Fin (m + 1) =>
    (Nat.fast_choose m (i : ℕ) : ℤ) * a ^ (m - (i : ℕ)))

def fastSplineCoeffsAux (n k : ℕ) : ℕ → Pure.IntPoly
  | 0 => []
  | m + 1 => Pure.Dense.add (fastSplineCoeffsAux n k m)
      (Pure.Dense.scale ((-1 : ℤ) ^ m * (Nat.fast_choose n m : ℤ))
        (binomialPowerCoeffs ((k : ℤ) - (m : ℤ)) (n - 1)))

def fastSplineCoeffs (n k : ℕ) : Pure.IntPoly := fastSplineCoeffsAux n k (k + 1)

def FastCellArithmeticValid (c : Pure.CellData) : Prop :=
  7 ≤ c.n ∧ c.n ≤ 149 ∧ 2 * c.k < c.n ∧
    (c.halfCell = true ↔ 2 * c.k + 1 = c.n) ∧
    c.degreeBound ≤ 3 * c.n - 2 ∧
    c.rCoeffs.length ≤ c.degreeBound + 1 ∧
    c.pCoeffs = fastSplineCoeffs c.n c.k ∧
    c.rCoeffs = Pure.curvatureCoeffs c.n c.k c.pCoeffs ∧
    c.transformedCoeffs =
      if c.halfCell then Pure.halfTransform c.degreeBound c.rCoeffs else c.rCoeffs

instance (c : Pure.CellData) : Decidable (FastCellArithmeticValid c) := by
  unfold FastCellArithmeticValid
  infer_instance

def fastCheckCell (c : Pure.CellData) : Bool :=
  decide (FastCellArithmeticValid c) &&
    Pure.checkBernsteinHorner c.degreeBound c.transformedCoeffs c.bernsteinNumerators

end ENT.Certificate.PureFast
