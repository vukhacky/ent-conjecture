module

public import ENT.Certificate.Pure
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Zip

/-! Pure rational remainder certificates. The records and Valid predicates mirror
ENT.Small.Quadrature exactly; PureRemainderSoundness proves the adapter. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Small.PureRemainder
open ENT.Certificate.Pure

def evalRat (p : IntPoly) (x : ℚ) : ℚ :=
  p.foldr (fun a acc => (a : ℚ) + x * acc) 0

def polynomialBounds (p : IntPoly) (a b : ℚ) : ℚ × ℚ :=
  match p with
  | [] => (0,0)
  | c::p =>
    let v := polynomialBounds p a b
    ((c:ℚ)+min (a*v.1) (b*v.1), (c:ℚ)+max (a*v.2) (b*v.2))

structure DerivativeBox where
  n : ℕ
  k : ℕ
  a : ℚ
  b : ℚ
  densityCoeffs : IntPoly
  numeratorCoeffs : IntPoly
  bound : ℚ

def DerivativeBox.Valid (c : DerivativeBox) : Prop :=
  5 ≤ c.n ∧ c.k ≤ c.n ∧ 0 ≤ c.a ∧ c.a < c.b ∧ c.b ≤ 1 ∧
  c.densityCoeffs = splineCoeffs c.n c.k ∧
  c.numeratorCoeffs = logarithmicNumeratorCoeffs c.densityCoeffs ∧
  0 < (polynomialBounds c.densityCoeffs c.a c.b).1 ∧ 0 ≤ c.bound ∧
  max |(polynomialBounds c.numeratorCoeffs c.a c.b).1|
      |(polynomialBounds c.numeratorCoeffs c.a c.b).2| ≤
    c.bound*((polynomialBounds c.densityCoeffs c.a c.b).1)^3

instance (c : DerivativeBox) : Decidable c.Valid := by
  unfold DerivativeBox.Valid
  infer_instance

structure DerivativeGrid where
  n : ℕ
  mesh : ℕ
  start : ℕ
  boxes : List DerivativeBox

def DerivativeGrid.node (g : DerivativeGrid) (i : ℕ) : ℚ :=
  ((g.start+i:ℕ):ℚ)/(g.mesh:ℚ)

def DerivativeGrid.Valid (g : DerivativeGrid) : Prop :=
  0 < g.mesh ∧ ∀ i : Fin g.boxes.length,
    (g.boxes.get i).Valid ∧ (g.boxes.get i).n = g.n ∧
    ((g.boxes.get i).k:ℚ)+(g.boxes.get i).a = g.node i ∧
    ((g.boxes.get i).k:ℚ)+(g.boxes.get i).b = g.node (i+1)

instance (g : DerivativeGrid) : Decidable g.Valid := by
  unfold DerivativeGrid.Valid
  infer_instance

structure ExpandedStep where
  a : ℚ
  b : ℚ
  gamma : ℚ
  bound : ℚ

def ExpandedStep.lowerLimit (c : ExpandedStep) : ℚ := (1-c.gamma)*c.a
def ExpandedStep.upperLimit (c : ExpandedStep) (n : ℕ) : ℚ :=
  min ((n:ℚ)/2) ((1+c.gamma)*c.b)

def ExpandedStep.Valid (c : ExpandedStep) (g : DerivativeGrid) : Prop :=
  0 ≤ c.bound ∧ g.node 0 < c.lowerLimit ∧ c.upperLimit g.n ≤ g.node g.boxes.length ∧
  g.boxes.all (fun box => decide (
    (((box.k:ℚ)+box.a < c.upperLimit g.n ∧ c.lowerLimit ≤ (box.k:ℚ)+box.b) →
      box.bound ≤ c.bound))) = true

instance (c : ExpandedStep) (g : DerivativeGrid) : Decidable (c.Valid g) := by
  unfold ExpandedStep.Valid
  infer_instance

structure CubeAreaCertificate where
  n : ℕ
  k : ℕ
  a : ℚ
  b : ℚ
  coeffs : IntPoly
  primitiveCoeffs : IntPoly
  primitiveDenominator : ℤ
  area : ℚ

def CubeAreaCertificate.Valid (c : CubeAreaCertificate) : Prop :=
  2 ≤ c.n ∧ c.k ≤ c.n ∧ 0 ≤ c.a ∧ c.a ≤ c.b ∧ c.b ≤ 1 ∧
  c.coeffs = Dense.mul (splineCoeffs c.n c.k) (Dense.power [(c.k:ℤ),1] 3) ∧
  0 < c.primitiveDenominator ∧
  Dense.derivative c.primitiveCoeffs = Dense.scale c.primitiveDenominator c.coeffs ∧
  c.area = (evalRat c.primitiveCoeffs c.b - evalRat c.primitiveCoeffs c.a)/
    (c.primitiveDenominator:ℚ)/(Nat.factorial (c.n-1):ℚ)

instance (c : CubeAreaCertificate) : Decidable c.Valid := by
  unfold CubeAreaCertificate.Valid
  infer_instance

def gridCondition (g : DerivativeGrid) (bi : DerivativeBox × ℕ) : Prop :=
  bi.1.Valid ∧ bi.1.n = g.n ∧
    (bi.1.k : ℚ) + bi.1.a = g.node bi.2 ∧
    (bi.1.k : ℚ) + bi.1.b = g.node (bi.2 + 1)

instance (g : DerivativeGrid) (bi : DerivativeBox × ℕ) :
    Decidable (gridCondition g bi) := by
  unfold gridCondition
  infer_instance

theorem gridValid_of_all (g : DerivativeGrid) (hmesh : 0 < g.mesh)
    (h : g.boxes.zipIdx.all (fun bi => decide (gridCondition g bi)) = true) :
    g.Valid := by
  refine ⟨hmesh, ?_⟩
  intro i
  have hall : ∀ bi ∈ g.boxes.zipIdx, gridCondition g bi := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using h
  apply hall (g.boxes.get i, (i : ℕ))
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  simp only [List.get_eq_getElem, List.getElem?_eq_getElem i.isLt]

theorem get_valid_of_all {α : Type*} {p : α → Prop} [DecidablePred p]
    (xs : List α) (h : xs.all (fun x => decide (p x)) = true) (i : Fin xs.length) :
    p (xs.get i) := by
  have hall : ∀ x ∈ xs, p x := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using h
  exact hall _ (List.get_mem _ _)

end ENT.Small.PureRemainder
