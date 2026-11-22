module

public import Init

/-! Integer arithmetic for packed cell certificates. `KroneckerLiteSoundness` identifies these definitions with the polynomial checker. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace ENT.Certificate.KroneckerLite

abbrev IntPoly := List Int

structure CellData where
  n : Nat
  k : Nat
  degreeBound : Nat
  halfCell : Bool
  pCoeffs : IntPoly
  rCoeffs : IntPoly
  transformedCoeffs : IntPoly
  bernsteinNumerators : List Int

def factorial : Nat → Nat
  | 0 => 1
  | Nat.succ n => Nat.succ n * factorial n

def descFactorial (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (n - k) * descFactorial n k

def fastChoose (n k : Nat) : Nat := descFactorial n k / factorial k

namespace Dense

def add : IntPoly → IntPoly → IntPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : Int) (p : IntPoly) : IntPoly := p.map (fun b => a * b)

def derivative : IntPoly → IntPoly
  | [] => []
  | [_] => []
  | _ :: b :: p => add (b :: p) (0 :: derivative (b :: p))

end Dense

def binomialPowerCoeffs (a : Int) (m : Nat) : IntPoly :=
  List.ofFn (fun i : Fin (m + 1) =>
    (fastChoose m (i : Nat) : Int) * a ^ (m - (i : Nat)))

def fastSplineCoeffsAux (n k : Nat) : Nat → IntPoly
  | 0 => []
  | m + 1 => Dense.add (fastSplineCoeffsAux n k m)
      (Dense.scale ((-1 : Int) ^ m * (fastChoose n m : Int))
        (binomialPowerCoeffs ((k : Int) - (m : Int)) (n - 1)))

def fastSplineCoeffs (n k : Nat) : IntPoly := fastSplineCoeffsAux n k (k + 1)

def halfTransform (d : Nat) : IntPoly → IntPoly
  | [] => []
  | a :: p => ((2 : Int) ^ d * a) :: halfTransform (d - 1) p

def sumAbs (p : List Int) : Nat := (p.map Int.natAbs).sum

def tripleFactor (d : Nat) : Nat := (3 * d + 1) * (2 * d + 1)

def curvatureCoeffBound (n k d M : Nat) : Nat :=
  tripleFactor d * M ^ 3 * (6 * n ^ 3 * d ^ 3 + 56 * (n + 2 * k) + 112)

def bernsteinCoeffBound (D : Nat) (bs : List Int) : Nat := sumAbs bs * 2 ^ D

def intEval (x : Int) : IntPoly → Int
  | [] => 0
  | a :: p => a + x * intEval x p

def bernsteinEvalPair (x : Int) : List Int → Int × Int
  | [] => (1, 0)
  | b :: bs =>
      let prev := bernsteinEvalPair x bs
      ((1 - x) * prev.1, b * prev.1 + x * prev.2)

def curvatureEval (n k : Nat) (p : IntPoly) (x : Int) : Int :=
  let d := Dense.derivative p
  let e := Dense.derivative d
  let f := Dense.derivative e
  let P := intEval x p
  let D := intEval x d
  let E := intEval x e
  let F := intEval x f
  (n : Int)^3 * (P^2 * F - 3 * P * D * E + 2 * D^3) -
    56 * ((n : Int) - 2 * (k : Int) - 2*x) * P^3

structure Valid (c : CellData) (rBase bBase : Int) : Prop where
  n_lower : 7 ≤ c.n
  n_upper : c.n ≤ 149
  cell : 2 * c.k < c.n
  half : c.halfCell = true ↔ 2 * c.k + 1 = c.n
  degree : c.degreeBound ≤ 3 * c.n - 2
  r_length : c.rCoeffs.length ≤ c.degreeBound + 1
  spline : c.pCoeffs = fastSplineCoeffs c.n c.k
  r_bound : sumAbs c.rCoeffs +
    curvatureCoeffBound c.n c.k c.pCoeffs.length (sumAbs c.pCoeffs) < rBase.natAbs
  r_eval : intEval rBase c.rCoeffs = curvatureEval c.n c.k c.pCoeffs rBase
  transform : c.transformedCoeffs =
    if c.halfCell then halfTransform c.degreeBound c.rCoeffs else c.rCoeffs
  b_length : c.bernsteinNumerators.length = c.degreeBound + 1
  b_bound : sumAbs c.transformedCoeffs +
    bernsteinCoeffBound c.degreeBound c.bernsteinNumerators < bBase.natAbs
  b_eval : intEval bBase c.transformedCoeffs =
    (bernsteinEvalPair bBase c.bernsteinNumerators).2
  nonneg : c.bernsteinNumerators.all (fun b => decide (0 ≤ b)) = true

end ENT.Certificate.KroneckerLite
