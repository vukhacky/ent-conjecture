module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Int.Basic

/-! Integer arithmetic for cell certificates. The equivalence with the polynomial checker is proved in `PureSoundness`. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Certificate.Pure

abbrev IntPoly := List ℤ

structure CellData where
  n : ℕ
  k : ℕ
  degreeBound : ℕ
  halfCell : Bool
  pCoeffs : IntPoly
  rCoeffs : IntPoly
  transformedCoeffs : IntPoly
  bernsteinNumerators : List ℤ

namespace Dense

def add : IntPoly → IntPoly → IntPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℤ) (p : IntPoly) : IntPoly := p.map (fun b => a * b)

def mul : IntPoly → IntPoly → IntPoly
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

def power (p : IntPoly) : ℕ → IntPoly
  | 0 => [1]
  | n + 1 => mul p (power p n)

def derivative : IntPoly → IntPoly
  | [] => []
  | [_] => []
  | _ :: b :: p => add (b :: p) (0 :: derivative (b :: p))

end Dense

def splineCoeffsAux (n k : ℕ) : ℕ → IntPoly
  | 0 => []
  | m + 1 => Dense.add (splineCoeffsAux n k m)
      (Dense.scale ((-1 : ℤ) ^ m * (Nat.fast_choose n m : ℤ))
        (Dense.power [(k : ℤ) - (m : ℤ), 1] (n - 1)))

def splineCoeffs (n k : ℕ) : IntPoly := splineCoeffsAux n k (k + 1)

def logarithmicNumeratorCoeffs (p : IntPoly) : IntPoly :=
  Dense.add
    (Dense.add
      (Dense.mul (Dense.power p 2) (Dense.derivative (Dense.derivative (Dense.derivative p))))
      (Dense.scale (-3)
        (Dense.mul (Dense.mul p (Dense.derivative p)) (Dense.derivative (Dense.derivative p)))))
    (Dense.scale 2 (Dense.power (Dense.derivative p) 3))

def curvatureCoeffs (n k : ℕ) (p : IntPoly) : IntPoly :=
  Dense.add (Dense.scale ((n : ℤ) ^ 3) (logarithmicNumeratorCoeffs p))
    (Dense.scale (-56)
      (Dense.mul [(n : ℤ) - 2 * (k : ℤ), -2] (Dense.power p 3)))

def halfTransform (d : ℕ) : IntPoly → IntPoly
  | [] => []
  | a :: p => ((2 : ℤ) ^ d * a) :: halfTransform (d - 1) p

def bernsteinHorner : List ℤ → IntPoly × IntPoly
  | [] => ([1], [])
  | [b] => ([1], [b])
  | b :: c :: bs =>
      let prev := bernsteinHorner (c :: bs)
      let nextPower := Dense.mul [1, -1] prev.1
      (nextPower, Dense.add (Dense.scale b nextPower) (0 :: prev.2))

def checkBernsteinHorner (d : ℕ) (p : IntPoly) (bs : List ℤ) : Bool :=
  decide (bs.length = d + 1) &&
    ((p == (bernsteinHorner bs).2) && bs.all (fun b => decide (0 ≤ b)))

def CellArithmeticValid (c : CellData) : Prop :=
  7 ≤ c.n ∧ c.n ≤ 149 ∧ 2 * c.k < c.n ∧
    (c.halfCell = true ↔ 2 * c.k + 1 = c.n) ∧
    c.degreeBound ≤ 3 * c.n - 2 ∧
    c.rCoeffs.length ≤ c.degreeBound + 1 ∧
    c.pCoeffs = splineCoeffs c.n c.k ∧
    c.rCoeffs = curvatureCoeffs c.n c.k c.pCoeffs ∧
    c.transformedCoeffs =
      if c.halfCell then halfTransform c.degreeBound c.rCoeffs else c.rCoeffs

instance (c : CellData) : Decidable (CellArithmeticValid c) := by
  unfold CellArithmeticValid
  infer_instance

def checkCell (c : CellData) : Bool :=
  decide (CellArithmeticValid c) &&
    checkBernsteinHorner c.degreeBound c.transformedCoeffs c.bernsteinNumerators

end ENT.Certificate.Pure
