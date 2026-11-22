module

public import ENT.Small.QuadraturePolynomials
public import ENT.Small.EnclosuresCertificate

/-! Complete finite witnesses for genuine exponential-polynomial cell integrals. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Small.Quadrature

open Certificate

def W3IntegerCoeffs : IntPoly := [0, 0, 34500, 0, 8100, 0, -2260, 0, 221]
def W3Denominator : ℤ := 100000
def W4IntegerCoeffs : IntPoly := [0, 0, 406500, 0, 30100, 0, -5630, 0, 518]
def W4Denominator : ℤ := 1000000
def W5IntegerCoeffs : IntPoly := [0, 0, 43346000, 0, 1535000, 0, -176900, 0, 17206]
def W5Denominator : ℤ := 100000000
def W6IntegerCoeffs : IntPoly := [0, 0, 44749000, 0, 1001000, 0, -64930, 0, 7284]
def W6Denominator : ℤ := 100000000

structure QuadratureCell where
  a : ℚ
  b : ℚ
  radius : ℚ
  denScale : ℤ
  centerNumerator : ℤ
  argumentCoeffs : IntPoly
  taylorCoeffs : IntPoly
  primitiveCoeffs : IntPoly
  primitiveDenominator : ℤ
  expPoint : Enclosures.ExpPointCertificate
  integralValue : ℚ
  upper : ℚ

def QuadratureCell.center (c : QuadratureCell) (wDen : ℤ) : ℚ :=
  (c.centerNumerator : ℚ) / ((wDen * c.denScale : ℤ) : ℚ)

def QuadratureCell.Valid (c : QuadratureCell) (w : IntPoly) (wDen : ℤ) : Prop :=
  0 < wDen ∧ 0 < c.denScale ∧ 0 ≤ c.a ∧ c.a ≤ c.b ∧ 0 ≤ c.radius ∧ c.radius ≤ 1 ∧
  c.argumentCoeffs = Dense.add [c.centerNumerator] (Dense.scale (-c.denScale) w) ∧
  c.taylorCoeffs = expTaylorInt10 (wDen * c.denScale) c.argumentCoeffs ∧
  0 < c.primitiveDenominator ∧
  Dense.derivative c.primitiveCoeffs = Dense.scale c.primitiveDenominator c.taylorCoeffs ∧
  c.expPoint.Valid ∧ c.expPoint.argument = -c.center wDen ∧
  c.center wDen - evalRat w c.a / (wDen : ℚ) ≤ c.radius ∧
  evalRat w c.b / (wDen : ℚ) - c.center wDen ≤ c.radius ∧
  c.integralValue = (evalRat c.primitiveCoeffs c.b - evalRat c.primitiveCoeffs c.a) /
    (c.primitiveDenominator : ℚ) / (362880 * ((wDen * c.denScale : ℤ) : ℚ) ^ 9) ∧
  0 ≤ c.integralValue - (c.b - c.a) * Enclosures.ratExpError 10 c.radius ∧
  c.expPoint.upper * (c.integralValue + (c.b - c.a) * Enclosures.ratExpError 10 c.radius) ≤ c.upper

instance (c : QuadratureCell) (w : IntPoly) (wDen : ℤ) : Decidable (c.Valid w wDen) := by
  unfold QuadratureCell.Valid
  infer_instance

noncomputable section

def rationalPolynomial (w : IntPoly) (wDen : ℤ) (x : ℝ) : ℝ := eval w x / (wDen : ℝ)

theorem QuadratureCell.argument_identity (c : QuadratureCell) (w : IntPoly) (wDen : ℤ)
    (hw : wDen ≠ 0) (hs : c.denScale ≠ 0)
    (hp : c.argumentCoeffs = Dense.add [c.centerNumerator] (Dense.scale (-c.denScale) w))
    (x : ℝ) :
    eval c.argumentCoeffs x / ((wDen * c.denScale : ℤ) : ℝ) =
      (c.center wDen : ℝ) - rationalPolynomial w wDen x := by
  have hwR : (wDen : ℝ) ≠ 0 := by exact_mod_cast hw
  have hsR : (c.denScale : ℝ) ≠ 0 := by exact_mod_cast hs
  rw [hp, Dense.eval_add, Dense.eval_cons, Dense.eval_nil, Dense.eval_scale]
  unfold QuadratureCell.center rationalPolynomial
  push_cast
  field_simp [hwR, hsR]
  <;> ring

/-- A proved certificate concludes an actual Bochner interval integral bound.
The only global analytic input is monotonicity of the specified polynomial. -/
theorem QuadratureCell.sound (c : QuadratureCell) (w : IntPoly) (wDen : ℤ)
    (hc : c.Valid w wDen)
    (hmono : MonotoneOn (rationalPolynomial w wDen) (Ici (0 : ℝ))) :
    (∫ x in (c.a : ℝ)..(c.b : ℝ), Real.exp (-rationalPolynomial w wDen x)) ≤
      (c.upper : ℝ) := by
  rcases hc with ⟨hw, hscale, ha, hab, hr0, hr1, hp, hQ, hM, hF, hexp, hxexp, hleft, hright, hS, hS0, hU⟩
  have hwR : (0 : ℝ) < wDen := by exact_mod_cast hw
  have hD : wDen * c.denScale ≠ 0 := (mul_pos hw hscale).ne'
  have haR : (0 : ℝ) ≤ c.a := by exact_mod_cast ha
  have habR : (c.a : ℝ) ≤ c.b := by exact_mod_cast hab
  have hr0R : (0 : ℝ) ≤ c.radius := by exact_mod_cast hr0
  have hr1R : (c.radius : ℝ) ≤ 1 := by exact_mod_cast hr1
  have hleftR : (c.center wDen : ℝ) - rationalPolynomial w wDen (c.a : ℝ) ≤ (c.radius : ℝ) := by
    have h : (((c.center wDen - evalRat w c.a / (wDen : ℚ)) : ℚ) : ℝ) ≤ (c.radius : ℝ) := by exact_mod_cast hleft
    push_cast at h
    rw [evalRat_cast] at h
    exact h
  have hrightR : rationalPolynomial w wDen (c.b : ℝ) - (c.center wDen : ℝ) ≤ (c.radius : ℝ) := by
    have h : (((evalRat w c.b / (wDen : ℚ) - c.center wDen) : ℚ) : ℝ) ≤ (c.radius : ℝ) := by exact_mod_cast hright
    push_cast at h
    rw [evalRat_cast] at h
    exact h
  have hlocal (x : ℝ) (hx : x ∈ Icc (c.a : ℝ) (c.b : ℝ)) :
      |(c.center wDen : ℝ) - rationalPolynomial w wDen x| ≤ (c.radius : ℝ) := by
    have hx0 : 0 ≤ x := haR.trans hx.1
    have hb0 : (0 : ℝ) ≤ c.b := haR.trans habR
    have hl := hmono haR hx0 hx.1
    have hu := hmono hx0 hb0 hx.2
    apply abs_le.mpr
    constructor <;> linarith
  have he := c.expPoint.sound hexp
  rw [hxexp] at he
  simp only [Rat.cast_neg] at he
  have harg := c.argument_identity w wDen hw.ne' hscale.ne' hp
  have hs := expTaylor10_integral_eq hD hM.ne' harg hQ hF c.a c.b
  rw [← hS] at hs
  have hs0 : 0 ≤ (c.integralValue : ℝ) - ((c.b : ℝ) - (c.a : ℝ)) * Enclosures.expError 10 (c.radius : ℝ) := by
    have h : (0 : ℝ) ≤ ((c.integralValue - (c.b - c.a) * Enclosures.ratExpError 10 c.radius : ℚ) : ℝ) :=
      by exact_mod_cast hS0
    push_cast at h
    rwa [Enclosures.ratExpError_cast] at h
  have hu : (c.expPoint.upper : ℝ) *
      ((c.integralValue : ℝ) + ((c.b : ℝ) - (c.a : ℝ)) * Enclosures.expError 10 (c.radius : ℝ)) ≤ (c.upper : ℝ) := by
    have h : ((c.expPoint.upper * (c.integralValue + (c.b - c.a) * Enclosures.ratExpError 10 c.radius) : ℚ) : ℝ) ≤
        (c.upper : ℝ) := by exact_mod_cast hU
    push_cast at h
    rwa [Enclosures.ratExpError_cast] at h
  have hW : Continuous (rationalPolynomial w wDen) := (continuous_dense_eval w).div_const _
  exact (exp_cell_integral_enclosure hW (by norm_num : 0 < (10 : ℕ)) habR
    hr0R hr1R hlocal he hs hs0).2.trans hu

end
end ENT.Small.Quadrature
