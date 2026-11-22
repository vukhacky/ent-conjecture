module

public import ENT.Small.PureRemainder
public import ENT.Certificate.PureSoundness
public import ENT.Small.RemainderAssembly

/-! The rational remainder checks imply the corresponding quadrature conditions. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Small.PureRemainder
open ENT.Certificate.Pure

private theorem polynomialBounds_eq (p : IntPoly) (a b : ℚ) :
    polynomialBounds p a b = Quadrature.polynomialBounds p a b := by
  induction p with
  | nil => rfl
  | cons c p ih => simp only [polynomialBounds, Quadrature.polynomialBounds, ih]

private theorem evalRat_eq (p : IntPoly) (x : ℚ) :
    evalRat p x = Quadrature.evalRat p x := rfl

def DerivativeBox.toSemantic (c : DerivativeBox) : Quadrature.DerivativeBox where
  n := c.n
  k := c.k
  a := c.a
  b := c.b
  densityCoeffs := c.densityCoeffs
  numeratorCoeffs := c.numeratorCoeffs
  bound := c.bound

theorem DerivativeBox.valid_iff (c : DerivativeBox) :
    c.Valid ↔ c.toSemantic.Valid := by
  simp only [DerivativeBox.Valid, Quadrature.DerivativeBox.Valid,
    DerivativeBox.toSemantic, spline_eq, numerator_eq, polynomialBounds_eq]

def DerivativeGrid.toSemantic (g : DerivativeGrid) : Quadrature.DerivativeGrid where
  n := g.n
  mesh := g.mesh
  start := g.start
  boxes := g.boxes.map DerivativeBox.toSemantic

@[simp] theorem DerivativeGrid.node_toSemantic (g : DerivativeGrid) (i : ℕ) :
    g.toSemantic.node i = g.node i := rfl

theorem DerivativeGrid.valid_toSemantic (g : DerivativeGrid) (hg : g.Valid) :
    g.toSemantic.Valid := by
  refine ⟨hg.1, ?_⟩
  intro i
  let j : Fin g.boxes.length := ⟨i, by simpa only [DerivativeGrid.toSemantic,
    List.length_map] using i.isLt⟩
  have h := hg.2 j
  have hget : g.toSemantic.boxes.get i = (g.boxes.get j).toSemantic := by
    exact List.getElem_map DerivativeBox.toSemantic
  rw [hget]
  exact ⟨(DerivativeBox.valid_iff (g.boxes.get j)).mp h.1,
    h.2.1, h.2.2.1, h.2.2.2⟩

def ExpandedStep.toSemantic (c : ExpandedStep) : Quadrature.ExpandedStep where
  a := c.a
  b := c.b
  gamma := c.gamma
  bound := c.bound

theorem ExpandedStep.valid_iff (c : ExpandedStep) (g : DerivativeGrid) :
    c.Valid g ↔ c.toSemantic.Valid g.toSemantic := by
  simp only [ExpandedStep.Valid, Quadrature.ExpandedStep.Valid,
    ExpandedStep.toSemantic, DerivativeGrid.toSemantic, List.length_map,
    ExpandedStep.lowerLimit, ExpandedStep.upperLimit,
    Quadrature.ExpandedStep.lowerLimit, Quadrature.ExpandedStep.upperLimit,
    Quadrature.DerivativeGrid.node, DerivativeGrid.node, List.all_map]
  rfl

def CubeAreaCertificate.toSemantic (c : CubeAreaCertificate) : Quadrature.CubeAreaCertificate where
  n := c.n
  k := c.k
  a := c.a
  b := c.b
  coeffs := c.coeffs
  primitiveCoeffs := c.primitiveCoeffs
  primitiveDenominator := c.primitiveDenominator
  area := c.area

theorem CubeAreaCertificate.valid_iff (c : CubeAreaCertificate) :
    c.Valid ↔ c.toSemantic.Valid := by
  simp only [CubeAreaCertificate.Valid, Quadrature.CubeAreaCertificate.Valid,
    CubeAreaCertificate.toSemantic, spline_eq, dense_mul_eq, dense_power_eq,
    dense_derivative_eq, dense_scale_eq, evalRat_eq]

theorem remainderBound_from_pure_grid (n : ℕ) (hn : 2 ≤ n) (N : ℕ)
    (g : DerivativeGrid) (hg : g.Valid) (hgn : g.n = n)
    (γ : ℚ) (hγ : (γ : ℝ) ∈ Set.Ico (0 : ℝ) 1)
    (d : ℚ) (hd : 0 ≤ d)
    (hformula : ∀ v ∈ Set.Ioc (0 : ℝ) 1, logThirdUnitSum n v = (d : ℝ) / v ^ 3)
    (S : Fin N → ExpandedStep) (A : Fin N → CubeAreaCertificate)
    (hS : ∀ i, (S i).Valid g) (hA : ∀ i, (A i).Valid)
    (hgeometry : ∀ i : Fin N,
      (S i).a = (1 / 2 : ℚ) + (i : ℚ) / 64 ∧
      (S i).b = (1 / 2 : ℚ) + ((i : ℚ) + 1) / 64 ∧
      (S i).gamma = γ ∧ (A i).n = n ∧
      ((A i).k : ℚ) + (A i).a = (S i).a ∧
      ((A i).k : ℚ) + (A i).b = (S i).b)
    (hend : (1 / 2 : ℚ) + (N : ℚ) / 64 = (n : ℚ) / 2)
    (U : ℚ)
    (hnumeric : 2 * (d / (1 - γ) ^ 3) *
        (1 / ((n : ℚ) * (Nat.factorial (n - 1) : ℚ) * 2 ^ n)) +
      2 * (∑ i : Fin N, (S i).bound * (A i).area) ≤ U) :
    ∃ H : LogThirdEnvelope n (γ : ℝ), averagedRemainderBound n H.bound ≤ (U : ℝ) := by
  exact remainderBound_from_grid n hn N g.toSemantic
    (g.valid_toSemantic hg) hgn γ hγ d hd hformula
    (fun i => (S i).toSemantic) (fun i => (A i).toSemantic)
    (fun i => ((S i).valid_iff g).mp (hS i))
    (fun i => (A i).valid_iff.mp (hA i)) hgeometry hend U hnumeric

end ENT.Small.PureRemainder
