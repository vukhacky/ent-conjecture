module

public import ENT.Small.EnclosuresThree
public import Mathlib.Data.Rat.Cast.Order
public import ENT.Small.QuadraturePolynomials
public import ENT.Small.Quadrature
public import ENT.Small.QuadratureCertificate
public import ENT.Small.EndpointLog
public import ENT.Small.LocalConstants
public import ENT.Entropy.SplineCoordinates
public import ENT.Spline.Symmetry
public import ENT.Certificate.CanonicalPolynomials
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import ENT.Certificate.LogDerivative
public import ENT.Spline.CellGluing
public import ENT.Spline.PositiveInterior
public import Mathlib.Order.Interval.Set.Union
public import ENT.Spline.Global

/-! Consolidated analytic and exact-arithmetic backend for small-dimensional scalar certificates.
The sections preserve their individual namespaces and theorem interfaces. -/

/-! ## EnclosuresLogCertificate -/
/-! Rational point certificates for logarithms, proved from a convergent finite series. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Small.Enclosures

def ratArtanhTaylor (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range n, x^(2*k+1) / (2*k+1 : ℕ)

def ratArtanhError (n : ℕ) (x : ℚ) : ℚ := x^(2*n+1)/(1-x^2)

structure LogPointCertificate where
  argument : ℚ
  shift : ℕ
  ratio : ℚ
  lower : ℚ
  upper : ℚ

def LogPointCertificate.Valid (c : LogPointCertificate) : Prop :=
  0 < c.argument ∧ 0 ≤ c.ratio ∧ c.ratio ≤ 1/2 ∧
  (1+c.ratio)/(1-c.ratio) = c.argument*2^c.shift ∧
  c.lower ≤ 2*ratArtanhTaylor 20 c.ratio - c.shift*(69314718057/100000000000:ℚ) ∧
  2*(ratArtanhTaylor 20 c.ratio + ratArtanhError 20 c.ratio) -
    c.shift*(69314718055/100000000000:ℚ) ≤ c.upper

instance (c : LogPointCertificate) : Decidable c.Valid := by
  unfold LogPointCertificate.Valid
  infer_instance

noncomputable section

theorem ratArtanhTaylor_cast (n : ℕ) (x : ℚ) :
    (ratArtanhTaylor n x : ℝ) = artanhTaylor n (x:ℝ) := by
  unfold ratArtanhTaylor artanhTaylor
  push_cast
  rfl

theorem ratArtanhError_cast (n : ℕ) (x : ℚ) :
    (ratArtanhError n x : ℝ) = artanhError n (x:ℝ) := by
  unfold ratArtanhError artanhError
  push_cast
  rfl

theorem LogPointCertificate.sound (c : LogPointCertificate) (hc : c.Valid) :
    (c.lower : ℝ) ≤ Real.log (c.argument : ℝ) ∧
      Real.log (c.argument : ℝ) ≤ (c.upper : ℝ) := by
  rcases hc with ⟨ha, hx0, hx1, he, hl, hu⟩
  have haR : (0:ℝ) < c.argument := by exact_mod_cast ha
  have hx0R : (0:ℝ) ≤ c.ratio := by exact_mod_cast hx0
  have hx1R : (c.ratio:ℝ) ≤ (1/2:ℝ) := by
    have h : (c.ratio:ℝ) ≤ ((1/2:ℚ):ℝ) := Rat.cast_le.mpr hx1
    norm_num at h
    exact h
  have heR : (1+(c.ratio:ℝ))/(1-(c.ratio:ℝ)) = (c.argument:ℝ)*2^c.shift := by
    exact_mod_cast he
  have h := log_ratio_taylor_bounds hx0R (by linarith : (c.ratio:ℝ)<1) 20
  rw [heR, Real.log_mul haR.ne' (by positivity), Real.log_pow] at h
  have hlR : (c.lower:ℝ) ≤ 2*artanhTaylor 20 (c.ratio:ℝ) -
      (c.shift:ℝ)*(69314718057/100000000000:ℝ) := by
    have h : (c.lower:ℝ) ≤ ((2*ratArtanhTaylor 20 c.ratio -
        c.shift*(69314718057/100000000000:ℚ) : ℚ):ℝ) := by exact_mod_cast hl
    push_cast at h
    simpa only [ratArtanhTaylor_cast] using h
  have huR : 2*(artanhTaylor 20 (c.ratio:ℝ) + artanhError 20 (c.ratio:ℝ)) -
      (c.shift:ℝ)*(69314718055/100000000000:ℝ) ≤ (c.upper:ℝ) := by
    have h : ((2*(ratArtanhTaylor 20 c.ratio + ratArtanhError 20 c.ratio) -
        c.shift*(69314718055/100000000000:ℚ) : ℚ):ℝ) ≤ (c.upper:ℝ) := by exact_mod_cast hu
    push_cast at h
    simpa only [ratArtanhTaylor_cast, ratArtanhError_cast] using h
  have hl2 := mul_le_mul_of_nonneg_left log_two_bounds.1 (Nat.cast_nonneg c.shift : (0:ℝ) ≤ c.shift)
  have hu2 := mul_le_mul_of_nonneg_left log_two_bounds.2 (Nat.cast_nonneg c.shift : (0:ℝ) ≤ c.shift)
  constructor <;> linarith

end
end ENT.Small.Enclosures

/-! ## EnclosuresPolynomial -/
/-! Whole-interval rational Horner enclosures; no sampling assumption occurs. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Small.Quadrature
open Certificate

def polynomialBounds (p : IntPoly) (a b : ℚ) : ℚ × ℚ :=
  match p with
  | [] => (0,0)
  | c::p =>
    let v := polynomialBounds p a b
    ((c:ℚ)+min (a*v.1) (b*v.1), (c:ℚ)+max (a*v.2) (b*v.2))

noncomputable section

 theorem min_mul_le_of_mem {a b x y : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    min (a*y) (b*y) ≤ x*y := by
  by_cases hy : 0 ≤ y
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy))

 theorem mul_le_max_of_mem {a b x y : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    x*y ≤ max (a*y) (b*y) := by
  by_cases hy : 0 ≤ y
  · exact (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy)).trans (le_max_left _ _)

 theorem polynomialBounds_sound (p : IntPoly) {a b : ℚ} (ha : 0 ≤ a)
    (x : ℝ) (hx : (a:ℝ) ≤ x ∧ x ≤ (b:ℝ)) :
    ((polynomialBounds p a b).1:ℝ) ≤ eval p x ∧
      eval p x ≤ ((polynomialBounds p a b).2:ℝ) := by
  have hx0 : 0 ≤ x := (show (0:ℝ) ≤ (a:ℝ) by exact_mod_cast ha).trans hx.1
  induction p with
  | nil => simp [polynomialBounds, eval]
  | cons c p ih =>
    simp only [polynomialBounds, Dense.eval_cons, Rat.cast_add,
      Rat.cast_min, Rat.cast_max, Rat.cast_mul, Rat.cast_intCast]
    have hl := mul_le_mul_of_nonneg_left ih.1 hx0
    have hu := mul_le_mul_of_nonneg_left ih.2 hx0
    constructor
    · have h := (min_mul_le_of_mem hx).trans hl
      linarith
    · have h := hu.trans (mul_le_max_of_mem hx)
      linarith

end
end ENT.Small.Quadrature

/-! ## QuadratureLogPolynomials -/
/-! Exact integer algebra for degree-sixteen logarithmic Taylor quadrature. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory

namespace ENT.Small.Quadrature
open Certificate

def logTaylorInt16 (D : ℤ) (p : IntPoly) : IntPoly :=
  let q16 := [-45045]
  let q15 := Dense.add [48048 * D ^ 1] (Dense.mul p q16)
  let q14 := Dense.add [-51480 * D ^ 2] (Dense.mul p q15)
  let q13 := Dense.add [55440 * D ^ 3] (Dense.mul p q14)
  let q12 := Dense.add [-60060 * D ^ 4] (Dense.mul p q13)
  let q11 := Dense.add [65520 * D ^ 5] (Dense.mul p q12)
  let q10 := Dense.add [-72072 * D ^ 6] (Dense.mul p q11)
  let q9 := Dense.add [80080 * D ^ 7] (Dense.mul p q10)
  let q8 := Dense.add [-90090 * D ^ 8] (Dense.mul p q9)
  let q7 := Dense.add [102960 * D ^ 9] (Dense.mul p q8)
  let q6 := Dense.add [-120120 * D ^ 10] (Dense.mul p q7)
  let q5 := Dense.add [144144 * D ^ 11] (Dense.mul p q6)
  let q4 := Dense.add [-180180 * D ^ 12] (Dense.mul p q5)
  let q3 := Dense.add [240240 * D ^ 13] (Dense.mul p q4)
  let q2 := Dense.add [-360360 * D ^ 14] (Dense.mul p q3)
  let q1 := Dense.add [720720 * D ^ 15] (Dense.mul p q2)
  Dense.mul p q1

def weightedLogPoly (weight p : IntPoly) (D qNum qDen : ℤ) : IntPoly :=
  Dense.mul weight (Dense.add [qNum*720720*D^16] (Dense.scale qDen (logTaylorInt16 D p)))

noncomputable section

theorem eval_logTaylorInt16 (D : ℤ) (hD : D ≠ 0) (p : IntPoly) (x : ℝ) :
    eval (logTaylorInt16 D p) x / (720720 * (D:ℝ)^16) =
      Enclosures.logTaylor 16 (eval p x / (D:ℝ)) := by
  have hDR : (D:ℝ) ≠ 0 := by exact_mod_cast hD
  unfold logTaylorInt16
  simp only [Dense.eval_add, Dense.eval_mul, Dense.eval_cons, Dense.eval_nil,
    mul_zero, add_zero, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_neg]
  norm_num [Enclosures.logTaylor, Finset.sum_range_succ]
  field_simp [hDR]
  <;> ring

theorem eval_weightedLogPoly (weight p : IntPoly) {D wDen qDen : ℤ}
    (hD : D ≠ 0) (hw : wDen ≠ 0) (hq : qDen ≠ 0) (qNum : ℤ) (x : ℝ) :
    eval (weightedLogPoly weight p D qNum qDen) x /
        ((wDen*qDen*720720*D^16:ℤ):ℝ) =
      (eval weight x / (wDen:ℝ)) *
        ((qNum:ℝ)/(qDen:ℝ) + Enclosures.logTaylor 16 (eval p x/(D:ℝ))) := by
  have hDR : (D:ℝ) ≠ 0 := by exact_mod_cast hD
  have hwR : (wDen:ℝ) ≠ 0 := by exact_mod_cast hw
  have hqR : (qDen:ℝ) ≠ 0 := by exact_mod_cast hq
  rw [← eval_logTaylorInt16 D hD p x]
  unfold weightedLogPoly
  simp only [Dense.eval_mul, Dense.eval_add, Dense.eval_cons, Dense.eval_nil,
    Dense.eval_scale, mul_zero, add_zero, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  field_simp [hDR, hwR, hqR]
  <;> ring

theorem integral_rationalPolynomial_of_primitive {p F : IntPoly} {D M : ℤ}
    (hM : M ≠ 0) (hF : Dense.derivative F = Dense.scale M p) (a b : ℚ) :
    (∫ x in (a:ℝ)..(b:ℝ), eval p x / (D:ℝ)) =
      (((evalRat F b - evalRat F a)/(M:ℚ)/(D:ℚ):ℚ):ℝ) := by
  rw [intervalIntegral.integral_div, integral_dense_of_primitive hM hF]
  push_cast
  rw [evalRat_cast, evalRat_cast]

end
end ENT.Small.Quadrature

/-! ## QuadratureLog -/
/-! Uniform polynomial quadrature for weighted logarithms on positive cells. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Small
noncomputable section

 theorem weighted_log_taylor_error {f w : ℝ → ℝ} {x c q δ r B : ℝ} {n : ℕ}
    (hc : 0 < c) (hf : 0 < f x) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (harg : |f x / c - 1| ≤ r) (hlog : |Real.log c - q| ≤ δ)
    (hweight : |w x| ≤ B) :
    |w x * Real.log (f x) -
      w x * (q + Enclosures.logTaylor n (f x/c-1))| ≤
        B * (δ + Enclosures.logError n r) := by
  have h := Enclosures.log_taylor_error (n:=n) hr0 hr1 harg
  have he : 1 + (f x / c - 1) = f x / c := by ring
  rw [he, Real.log_div hf.ne' hc.ne'] at h
  have he2 : Real.log (f x) - (q + Enclosures.logTaylor n (f x/c-1)) =
      (Real.log c - q) + (Real.log (f x) - Real.log c -
        Enclosures.logTaylor n (f x/c-1)) := by ring
  have hs : |Real.log (f x) - (q + Enclosures.logTaylor n (f x/c-1))| ≤
      δ + Enclosures.logError n r := by
    rw [he2]
    exact (abs_add_le _ _).trans (add_le_add hlog h)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul hweight hs (abs_nonneg _) ((abs_nonneg _).trans hweight)

 theorem weighted_log_integral_enclosure {f w p : ℝ → ℝ} {a b c q δ r B s : ℝ} {n : ℕ}
    (hab : a ≤ b) (hc : 0 < c) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Continuous f) (hw : Continuous w) (hp : Continuous p)
    (hfpos : ∀ x ∈ Icc a b, 0 < f x)
    (harg : ∀ x ∈ Icc a b, |f x/c-1| ≤ r)
    (hlog : |Real.log c - q| ≤ δ)
    (hweight : ∀ x ∈ Icc a b, |w x| ≤ B)
    (hpoly : ∀ x, p x = w x * (q + Enclosures.logTaylor n (f x/c-1)))
    (hs : (∫ x in a..b, p x) = s) :
    s - (b-a)*B*(δ+Enclosures.logError n r) ≤
        (∫ x in a..b, w x * Real.log (f x)) ∧
      (∫ x in a..b, w x * Real.log (f x)) ≤
        s + (b-a)*B*(δ+Enclosures.logError n r) := by
  have hlogcont : ContinuousOn (fun x => w x * Real.log (f x)) (Icc a b) :=
    hw.continuousOn.mul (hf.continuousOn.log (fun x hx => (hfpos x hx).ne'))
  have hi : IntervalIntegrable (fun x => w x * Real.log (f x)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (hlogcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have herr : ∀ x ∈ Icc a b, |w x * Real.log (f x) - p x| ≤
      B*(δ+Enclosures.logError n r) := by
    intro x hx
    rw [hpoly]
    exact weighted_log_taylor_error (n:=n) hc (hfpos x hx) hr0 hr1
      (harg x hx) hlog (hweight x hx)
  have h := integral_enclosure_of_uniform_error hab hi (hp.intervalIntegrable a b) herr hs
  constructor <;> nlinarith [h.1, h.2]

end
end ENT.Small

/-! ## QuadratureLogCertificate -/
/-! A complete finite certificate for a weighted logarithmic polynomial integral. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Small.Quadrature
open Certificate

def ratLogError (n : ℕ) (r : ℚ) : ℚ := r^(n+1)/(1-r)

structure LogQuadratureCell where
  a : ℚ
  b : ℚ
  radius : ℚ
  densityCoeffs : IntPoly
  densityDenominator : ℤ
  weightCoeffs : IntPoly
  weightDenominator : ℤ
  centerNumerator : ℤ
  centerDenominator : ℤ
  logPoint : Enclosures.LogPointCertificate
  logNumerator : ℤ
  logDenominator : ℤ
  logError : ℚ
  weightBound : ℚ
  argumentCoeffs : IntPoly
  integrandCoeffs : IntPoly
  primitiveCoeffs : IntPoly
  primitiveDenominator : ℤ
  integralValue : ℚ
  lower : ℚ
  upper : ℚ

def LogQuadratureCell.center (c : LogQuadratureCell) : ℚ :=
  (c.centerNumerator:ℚ)/(c.centerDenominator:ℚ)
def LogQuadratureCell.logCenter (c : LogQuadratureCell) : ℚ :=
  (c.logNumerator:ℚ)/(c.logDenominator:ℚ)
def LogQuadratureCell.argumentDenominator (c : LogQuadratureCell) : ℤ :=
  c.centerNumerator*c.densityDenominator
def LogQuadratureCell.integrandDenominator (c : LogQuadratureCell) : ℤ :=
  c.weightDenominator*c.logDenominator*720720*c.argumentDenominator^16

def LogQuadratureCell.Valid (c : LogQuadratureCell) : Prop :=
  0 ≤ c.a ∧ c.a ≤ c.b ∧ 0 ≤ c.radius ∧ c.radius < 1 ∧
  0 < c.densityDenominator ∧ 0 < c.weightDenominator ∧
  0 < c.centerNumerator ∧ 0 < c.centerDenominator ∧ 0 < c.logDenominator ∧
  c.logPoint.Valid ∧ c.logPoint.argument = c.center ∧
  c.logCenter - c.logError ≤ c.logPoint.lower ∧
  c.logPoint.upper ≤ c.logCenter + c.logError ∧
  0 < (polynomialBounds c.densityCoeffs c.a c.b).1 / (c.densityDenominator:ℚ) ∧
  1-c.radius ≤ ((polynomialBounds c.densityCoeffs c.a c.b).1 /
    (c.densityDenominator:ℚ))/c.center ∧
  ((polynomialBounds c.densityCoeffs c.a c.b).2 /
    (c.densityDenominator:ℚ))/c.center ≤ 1+c.radius ∧
  -c.weightBound ≤ (polynomialBounds c.weightCoeffs c.a c.b).1 / (c.weightDenominator:ℚ) ∧
  (polynomialBounds c.weightCoeffs c.a c.b).2 / (c.weightDenominator:ℚ) ≤ c.weightBound ∧
  c.argumentCoeffs = Dense.add (Dense.scale c.centerDenominator c.densityCoeffs)
    [-c.argumentDenominator] ∧
  c.integrandCoeffs = weightedLogPoly c.weightCoeffs c.argumentCoeffs
    c.argumentDenominator c.logNumerator c.logDenominator ∧
  0 < c.primitiveDenominator ∧
  Dense.derivative c.primitiveCoeffs = Dense.scale c.primitiveDenominator c.integrandCoeffs ∧
  c.integralValue = (evalRat c.primitiveCoeffs c.b - evalRat c.primitiveCoeffs c.a) /
    (c.primitiveDenominator:ℚ)/(c.integrandDenominator:ℚ) ∧
  c.lower ≤ c.integralValue - (c.b-c.a)*c.weightBound*(c.logError+ratLogError 16 c.radius) ∧
  c.integralValue + (c.b-c.a)*c.weightBound*(c.logError+ratLogError 16 c.radius) ≤ c.upper

instance (c : LogQuadratureCell) : Decidable c.Valid := by
  unfold LogQuadratureCell.Valid
  infer_instance

noncomputable section

theorem ratLogError_cast (n : ℕ) (r : ℚ) :
    (ratLogError n r:ℝ) = Enclosures.logError n (r:ℝ) := by
  unfold ratLogError Enclosures.logError
  push_cast
  rfl

theorem rationalPolynomial_bounds (p : IntPoly) {D : ℤ} (hD : 0 < D)
    {a b : ℚ} (ha : 0 ≤ a) (x : ℝ) (hx : (a:ℝ) ≤ x ∧ x ≤ (b:ℝ)) :
    (((polynomialBounds p a b).1 / (D:ℚ):ℚ):ℝ) ≤ rationalPolynomial p D x ∧
      rationalPolynomial p D x ≤ (((polynomialBounds p a b).2 / (D:ℚ):ℚ):ℝ) := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have h := polynomialBounds_sound p ha x hx
  unfold rationalPolynomial
  push_cast
  exact ⟨div_le_div_of_nonneg_right h.1 hDR.le, div_le_div_of_nonneg_right h.2 hDR.le⟩

theorem LogQuadratureCell.sound (c : LogQuadratureCell) (hc : c.Valid) :
    (c.lower:ℝ) ≤ (∫ x in (c.a:ℝ)..(c.b:ℝ),
      rationalPolynomial c.weightCoeffs c.weightDenominator x *
        Real.log (rationalPolynomial c.densityCoeffs c.densityDenominator x)) ∧
    (∫ x in (c.a:ℝ)..(c.b:ℝ),
      rationalPolynomial c.weightCoeffs c.weightDenominator x *
        Real.log (rationalPolynomial c.densityCoeffs c.densityDenominator x)) ≤ (c.upper:ℝ) := by
  rcases hc with ⟨ha, hab, hr0, hr1, hfd, hwd, hcn, hcd, hqd, hlog, hlogarg,
    hloglo, hloghi, hflo, hfarglo, hfarghi, hwlo, hwhi, harg, hpoly, hM, hF, hI, hlow, hupp⟩
  have hcnR : (0:ℝ) < c.centerNumerator := by exact_mod_cast hcn
  have hcdR : (0:ℝ) < c.centerDenominator := by exact_mod_cast hcd
  have hfdR : (0:ℝ) < c.densityDenominator := by exact_mod_cast hfd
  have hcR : (0:ℝ) < (c.center:ℝ) := by
    unfold LogQuadratureCell.center
    push_cast
    exact div_pos hcnR hcdR
  have hD : c.argumentDenominator ≠ 0 := (mul_pos hcn hfd).ne'
  have habR : (c.a:ℝ) ≤ c.b := by exact_mod_cast hab
  have hr0R : (0:ℝ) ≤ c.radius := by exact_mod_cast hr0
  have hr1R : (c.radius:ℝ) < 1 := by exact_mod_cast hr1
  have hfpos (x : ℝ) (hx : x ∈ Icc (c.a:ℝ) (c.b:ℝ)) :
      0 < rationalPolynomial c.densityCoeffs c.densityDenominator x := by
    exact lt_of_lt_of_le (by exact_mod_cast hflo)
      (rationalPolynomial_bounds c.densityCoeffs hfd ha x hx).1
  have hargR (x : ℝ) (hx : x ∈ Icc (c.a:ℝ) (c.b:ℝ)) :
      |rationalPolynomial c.densityCoeffs c.densityDenominator x / (c.center:ℝ) - 1| ≤
        (c.radius:ℝ) := by
    have hf := rationalPolynomial_bounds c.densityCoeffs hfd ha x hx
    have hl := div_le_div_of_nonneg_right hf.1 hcR.le
    have hu := div_le_div_of_nonneg_right hf.2 hcR.le
    have hl0 : 1-(c.radius:ℝ) ≤
        (((polynomialBounds c.densityCoeffs c.a c.b).1 / (c.densityDenominator:ℚ):ℚ):ℝ)/(c.center:ℝ) :=
      by exact_mod_cast hfarglo
    have hu0 : (((polynomialBounds c.densityCoeffs c.a c.b).2 / (c.densityDenominator:ℚ):ℚ):ℝ)/(c.center:ℝ) ≤
        1+(c.radius:ℝ) := by exact_mod_cast hfarghi
    apply abs_le.mpr
    constructor <;> linarith
  have hwR (x : ℝ) (hx : x ∈ Icc (c.a:ℝ) (c.b:ℝ)) :
      |rationalPolynomial c.weightCoeffs c.weightDenominator x| ≤ (c.weightBound:ℝ) := by
    have hw := rationalPolynomial_bounds c.weightCoeffs hwd ha x hx
    have hlo : -(c.weightBound:ℝ) ≤
        (((polynomialBounds c.weightCoeffs c.a c.b).1 / (c.weightDenominator:ℚ):ℚ):ℝ) := by exact_mod_cast hwlo
    have hhi : (((polynomialBounds c.weightCoeffs c.a c.b).2 / (c.weightDenominator:ℚ):ℚ):ℝ) ≤
        (c.weightBound:ℝ) := by exact_mod_cast hwhi
    exact abs_le.mpr ⟨hlo.trans hw.1, hw.2.trans hhi⟩
  have hl := c.logPoint.sound hlog
  rw [hlogarg] at hl
  have hlogR : |Real.log (c.center:ℝ) - (c.logCenter:ℝ)| ≤ (c.logError:ℝ) := by
    have hlo : (c.logCenter:ℝ) - (c.logError:ℝ) ≤ (c.logPoint.lower:ℝ) := by exact_mod_cast hloglo
    have hhi : (c.logPoint.upper:ℝ) ≤ (c.logCenter:ℝ) + (c.logError:ℝ) := by exact_mod_cast hloghi
    apply abs_le.mpr
    constructor <;> linarith [hl.1, hl.2]
  have hargid (x : ℝ) : eval c.argumentCoeffs x / (c.argumentDenominator:ℝ) =
      rationalPolynomial c.densityCoeffs c.densityDenominator x / (c.center:ℝ) - 1 := by
    rw [harg, Dense.eval_add, Dense.eval_scale, Dense.eval_cons, Dense.eval_nil]
    unfold rationalPolynomial LogQuadratureCell.center LogQuadratureCell.argumentDenominator
    push_cast
    field_simp [hcnR.ne', hcdR.ne', hfdR.ne']
    <;> ring
  have hpolyR (x : ℝ) :
      eval c.integrandCoeffs x / (c.integrandDenominator:ℝ) =
        rationalPolynomial c.weightCoeffs c.weightDenominator x *
          ((c.logCenter:ℝ) + Enclosures.logTaylor 16
            (rationalPolynomial c.densityCoeffs c.densityDenominator x / (c.center:ℝ) - 1)) := by
    rw [hpoly]
    unfold LogQuadratureCell.integrandDenominator
    rw [eval_weightedLogPoly _ _ hD hwd.ne' hqd.ne', hargid]
    unfold LogQuadratureCell.logCenter rationalPolynomial
    push_cast
    rfl
  have hIreal := integral_rationalPolynomial_of_primitive (D := c.integrandDenominator) hM.ne' hF c.a c.b
  rw [←hI] at hIreal
  have h := weighted_log_integral_enclosure habR hcR hr0R hr1R
    ((continuous_dense_eval c.densityCoeffs).div_const c.densityDenominator)
    ((continuous_dense_eval c.weightCoeffs).div_const c.weightDenominator)
    ((continuous_dense_eval c.integrandCoeffs).div_const c.integrandDenominator)
    hfpos hargR hlogR hwR hpolyR hIreal
  have hloR : (c.lower:ℝ) ≤ (c.integralValue:ℝ) -
      ((c.b:ℝ)-(c.a:ℝ))*(c.weightBound:ℝ)*((c.logError:ℝ)+Enclosures.logError 16 (c.radius:ℝ)) := by
    have h : (c.lower:ℝ) ≤ ((c.integralValue -
      (c.b-c.a)*c.weightBound*(c.logError+ratLogError 16 c.radius):ℚ):ℝ) := by exact_mod_cast hlow
    push_cast at h
    simpa only [ratLogError_cast] using h
  have hupR : (c.integralValue:ℝ) +
      ((c.b:ℝ)-(c.a:ℝ))*(c.weightBound:ℝ)*((c.logError:ℝ)+Enclosures.logError 16 (c.radius:ℝ)) ≤ (c.upper:ℝ) := by
    have h : ((c.integralValue +
      (c.b-c.a)*c.weightBound*(c.logError+ratLogError 16 c.radius):ℚ):ℝ) ≤ (c.upper:ℝ) := by exact_mod_cast hupp
    push_cast at h
    simpa only [ratLogError_cast] using h
  exact ⟨hloR.trans h.1, h.2.trans hupR⟩

theorem LogQuadratureCell.transfer (c : LogQuadratureCell) (hc : c.Valid)
    (f w : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (c.a:ℝ) (c.b:ℝ),
      f x = rationalPolynomial c.densityCoeffs c.densityDenominator x)
    (hw : ∀ x ∈ Icc (c.a:ℝ) (c.b:ℝ),
      w x = rationalPolynomial c.weightCoeffs c.weightDenominator x) :
    (c.lower:ℝ) ≤ (∫ x in (c.a:ℝ)..(c.b:ℝ), w x*Real.log (f x)) ∧
      (∫ x in (c.a:ℝ)..(c.b:ℝ), w x*Real.log (f x)) ≤ (c.upper:ℝ) := by
  have hab : (c.a:ℝ) ≤ c.b := by exact_mod_cast hc.2.1
  have he : (∫ x in (c.a:ℝ)..(c.b:ℝ), w x*Real.log (f x)) =
      ∫ x in (c.a:ℝ)..(c.b:ℝ),
        rationalPolynomial c.weightCoeffs c.weightDenominator x *
          Real.log (rationalPolynomial c.densityCoeffs c.densityDenominator x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    dsimp only
    rw [hf x hx,hw x hx]
  rw [he]
  exact c.sound hc

end
end ENT.Small.Quadrature

/-! ## QuadratureSpline -/
/-! Exact coordinate, symmetry and outer-cell identities for scalar spline certificates. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Small
noncomputable section
open Spline Certificate Quadrature

theorem unitSumSplineDensity_eq_rationalPolynomial (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    unitSumSplineDensity n ((k:ℝ)+s) =
      rationalPolynomial (splineCoeffs n k) (Nat.factorial (n-1):ℤ) s := by
  rw [unitSumSplineDensity, unnormalizedSpline_eq_piece n k hn hk s hs0 hs1]
  unfold rationalPolynomial
  rw [splineCoeffs_eval]
  push_cast
  ring

theorem entropy_logQuadrature_bound (c : LogQuadratureCell) (hc : c.Valid)
    (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n)
    (hp : c.densityCoeffs = splineCoeffs n k)
    (hD : c.densityDenominator = (Nat.factorial (n-1):ℤ))
    (hw : c.weightCoeffs = c.densityCoeffs) (hwd : c.weightDenominator = c.densityDenominator)
    (hb : c.b ≤ 1) :
    (c.lower:ℝ) ≤ (∫ x in ((k:ℝ)+(c.a:ℝ))..((k:ℝ)+(c.b:ℝ)),
      unitSumSplineDensity n x * Real.log (unitSumSplineDensity n x)) ∧
    (∫ x in ((k:ℝ)+(c.a:ℝ))..((k:ℝ)+(c.b:ℝ)),
      unitSumSplineDensity n x * Real.log (unitSumSplineDensity n x)) ≤ (c.upper:ℝ) := by
  have haR : (0:ℝ) ≤ c.a := by exact_mod_cast hc.1
  have hbR : (c.b:ℝ) ≤ 1 := by exact_mod_cast hb
  have hf (x : ℝ) (hx : x ∈ Icc (c.a:ℝ) (c.b:ℝ)) :
      unitSumSplineDensity n ((k:ℝ)+x) =
        rationalPolynomial c.densityCoeffs c.densityDenominator x := by
    rw [hp,hD]
    exact unitSumSplineDensity_eq_rationalPolynomial n k hn hk x (haR.trans hx.1) (hx.2.trans hbR)
  have h := c.transfer hc (fun x => unitSumSplineDensity n ((k:ℝ)+x))
    (fun x => unitSumSplineDensity n ((k:ℝ)+x)) hf
    (fun x hx => by rw [hw,hwd]; exact hf x hx)
  have hcomp := intervalIntegral.integral_comp_add_left
    (f:=fun x : ℝ => unitSumSplineDensity n x*Real.log (unitSumSplineDensity n x))
    (a:=(c.a:ℝ)) (b:=(c.b:ℝ)) (k:ℝ)
  rw [hcomp] at h
  exact h

theorem unitSumSplineDensity_outer (n : ℕ) (hn : 2 ≤ n) (t : ℝ)
    (ht : t ∈ Icc (0:ℝ) 1) :
    unitSumSplineDensity n t = t^(n-1)/(Nat.factorial (n-1):ℝ) := by
  have h := unnormalizedSpline_eq_piece n 0 hn (by omega) t ht.1 ht.2
  simp only [Nat.cast_zero, zero_add] at h
  rw [unitSumSplineDensity,h]
  simp only [splinePiece, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.cast_zero, zero_add, sub_zero, pow_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul]
  ring

theorem continuous_pow_mul_log (m : ℕ) (hm : 0 < m) :
    Continuous (fun x : ℝ => x^m * Real.log x) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have he : (fun x : ℝ => x^(k+1)*Real.log x) = (fun x => x^k*(x*Real.log x)) := by
    funext x
    rw [pow_succ]
    ring
  rw [he]
  exact (continuous_id.pow k).mul Real.continuous_mul_log

theorem integral_pow_mul_log_zero_one (m : ℕ) (hm : 0 < m) :
    (∫ x in (0:ℝ)..1, x^m * Real.log x) = -1/((m+1:ℕ):ℝ)^2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let D : ℝ := (k+2:ℕ)
  have hD : D ≠ 0 := by dsimp [D]; positivity
  let P : ℝ → ℝ := fun x => x^(k+1)*(x*Real.log x)/D - x^(k+2)/D^2
  have hc : Continuous P := by dsimp [P]; fun_prop
  have hd (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
      HasDerivAt P (x^(k+1)*Real.log x) x := by
    have h := ((((hasDerivAt_id x).pow (k+1)).mul
      (Real.hasDerivAt_mul_log hx.1.ne')).div_const D).sub
      (((hasDerivAt_id x).pow (k+2)).div_const (D^2))
    convert h using 1
    · rfl
    · simp only [Pi.pow_apply,id_eq,Nat.add_sub_cancel]
      simp only [D,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
      field_simp
      rw [show k+2-1=k+1 by omega, pow_succ]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    hc.continuousOn hd ((continuous_pow_mul_log (k+1) (by omega)).intervalIntegrable 0 1)]
  simp [P,D]
  ring

theorem unitSum_entropy_outer_integral (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in (0:ℝ)..1, unitSumSplineDensity n t * Real.log (unitSumSplineDensity n t)) =
      -((n-1:ℕ):ℝ)/((Nat.factorial (n-1):ℝ)*(n:ℝ)^2) -
        Real.log (Nat.factorial (n-1):ℝ)/((Nat.factorial (n-1):ℝ)*(n:ℝ)) := by
  have hfn : (0:ℝ) < (Nat.factorial (n-1):ℝ) := by positivity
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
  have hn1 : n-1+1=n := by omega
  have he : (∫ t in (0:ℝ)..1, unitSumSplineDensity n t * Real.log (unitSumSplineDensity n t)) =
      ∫ t in (0:ℝ)..1,
        (((n-1:ℕ):ℝ)/(Nat.factorial (n-1):ℝ))*(t^(n-1)*Real.log t) -
          (Real.log (Nat.factorial (n-1):ℝ)/(Nat.factorial (n-1):ℝ))*t^(n-1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at ht
    dsimp only
    rw [unitSumSplineDensity_outer n hn t ht]
    by_cases ht0 : t=0
    · simp [ht0,zero_pow (by omega : n-1≠0)]
    · rw [Real.log_div (pow_ne_zero _ ht0) hfn.ne',Real.log_pow]
      ring
  have hi1 : IntervalIntegrable (fun t : ℝ =>
      (((n-1:ℕ):ℝ)/(Nat.factorial (n-1):ℝ))*(t^(n-1)*Real.log t)) volume 0 1 :=
    ((continuous_pow_mul_log (n-1) (by omega)).const_mul _).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun t : ℝ =>
      (Real.log (Nat.factorial (n-1):ℝ)/(Nat.factorial (n-1):ℝ))*t^(n-1)) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow (n-1))).intervalIntegrable 0 1
  rw [he,intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_pow_mul_log_zero_one (n-1) (by omega), integral_pow,hn1]
  simp only [one_pow,zero_pow (by omega : n≠0),sub_zero]
  rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  field_simp [hnR,hfn.ne']
  <;> ring

theorem integral_reflection_half {f : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hf : IntervalIntegrable f volume 0 R) (heven : ∀ x, f (R-x)=f x) :
    (∫ x in (0:ℝ)..R, f x) = 2*(∫ x in (0:ℝ)..(R/2),f x) := by
  have he : (∫ x in (0:ℝ)..(R/2),f x) = ∫ x in (R/2)..R,f x := by
    have h := intervalIntegral.integral_comp_sub_left (f:=f) (a:=(0:ℝ)) (b:=R/2) R
    simp only [heven,sub_zero,show R-R/2=R/2 by ring] at h
    exact h
  have hhalf0 : 0 ≤ R/2 := by linarith
  have hhalfR : R/2 ≤ R := by linarith
  have hi1 : IntervalIntegrable f volume 0 (R/2) := hf.mono_set (by
    rw [uIcc_of_le hhalf0,uIcc_of_le hR]
    exact Icc_subset_Icc le_rfl hhalfR)
  have hi2 : IntervalIntegrable f volume (R/2) R := hf.mono_set (by
    rw [uIcc_of_le hhalfR,uIcc_of_le hR]
    exact Icc_subset_Icc hhalf0 le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [←hsplit,←he]
  ring

theorem unitSum_entropy_half (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in (0:ℝ)..(n:ℝ), unitSumSplineDensity n t * Real.log (unitSumSplineDensity n t)) =
      2*(∫ t in (0:ℝ)..((n:ℝ)/2), unitSumSplineDensity n t * Real.log (unitSumSplineDensity n t)) := by
  apply integral_reflection_half (by positivity)
    ((Real.continuous_mul_log.comp (continuous_unitSumSplineDensity n)).intervalIntegrable 0 n)
  intro x
  dsimp only [Function.comp_apply]
  rw [unitSumSplineDensity_reflection n hn]

end
end ENT.Small

/-! ## EnclosuresDerivative -/
/-! Whole-interval enclosures for the actual third logarithmic derivative of a spline. -/

@[expose] public section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace ENT.Small.Quadrature
open Certificate Spline

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

noncomputable section

theorem logThirdUnitSum_eq_piece_on_positive_box (n k : ℕ) (hn : 5 ≤ n) (hk : k ≤ n)
    {a b x : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hx : x ∈ Icc a b)
    (hp : ∀ s ∈ Icc a b, 0 < splinePiece n k s) :
    logThirdUnitSum n ((k:ℝ)+x) =
      eval (logarithmicNumeratorCoeffs (splineCoeffs n k)) x /
        (eval (splineCoeffs n k) x)^3 := by
  let D : ℝ := (Nat.factorial (n-1):ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  have heq : EqOn (fun s : ℝ => Real.log (unitSumSplineDensity n ((k:ℝ)+s)))
      (fun s => Real.log (splinePiece n k s)-Real.log D) (Icc a b) := by
    intro s hs
    have hs0 : 0 ≤ s := ha.trans hs.1
    have hs1 : s ≤ 1 := hs.2.trans hb
    dsimp only
    rw [unitSumSplineDensity,unnormalizedSpline_eq_piece n k (by omega) hk s hs0 hs1]
    change Real.log (D⁻¹ * splinePiece n k s) = _
    rw [Real.log_mul (inv_ne_zero hD.ne') (hp s hs).ne',Real.log_inv]
    ring
  have hx0 : 0 ≤ x := ha.trans hx.1
  have hx1 : x ≤ 1 := hx.2.trans hb
  have hglobal : unitSumSplineDensity n ((k:ℝ)+x) ≠ 0 := by
    rw [unitSumSplineDensity,unnormalizedSpline_eq_piece n k (by omega) hk x hx0 hx1]
    exact mul_ne_zero (by positivity) (hp x hx).ne'
  have hg : ContDiffAt ℝ 3 (fun s : ℝ => Real.log (unitSumSplineDensity n ((k:ℝ)+s))) x :=
    (((contDiff_unitSumSplineDensity 3 n (by omega)).comp
      (contDiff_const.add contDiff_id)).contDiffAt.log hglobal)
  have hh : ContDiffAt ℝ 3 (fun s => Real.log (splinePiece n k s)-Real.log D) x :=
    ((contDiff_splinePiece 3 n k).contDiffAt.log (hp x hx).ne').sub contDiffAt_const
  have hjet := iteratedDeriv_eq_of_eqOn_Icc 3 _ _ a b x hab hx hg hh heq
  have hshift := congrFun (iteratedDeriv_comp_const_add 3
    (fun z : ℝ => Real.log (unitSumSplineDensity n z)) (k:ℝ)) x
  rw [hshift] at hjet
  have hconstant : (fun s => Real.log (splinePiece n k s)-Real.log D) =
      (fun s => -Real.log D + Real.log (splinePiece n k s)) := by funext s; ring
  rw [hconstant,iteratedDeriv_const_add (by norm_num : 0 < (3:ℕ))] at hjet
  have hpoly := third_deriv_log_polynomial (splinePolynomial n k) x
    (by rw [splinePolynomial_eval]; exact (hp x hx).ne')
  have hfun : (fun s => (splinePolynomial n k).eval s) = splinePiece n k :=
    funext (splinePolynomial_eval n k)
  rw [logarithmicNumeratorPolynomial_eval,hfun] at hpoly
  simp_rw [splinePolynomial_eval] at hpoly
  have hdense : eval (splineCoeffs n k) = splinePiece n k := funext (splineCoeffs_eval n k)
  rw [logarithmicNumeratorCoeffs_eval,hdense]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hjet
  exact hjet.trans hpoly

theorem DerivativeBox.sound (c : DerivativeBox) (hc : c.Valid) (x : ℝ)
    (hx : x ∈ Icc (c.a:ℝ) (c.b:ℝ)) :
    |logThirdUnitSum c.n ((c.k:ℝ)+x)| ≤ (c.bound:ℝ) := by
  rcases hc with ⟨hn,hk,ha,hab,hb,hp,hN,hP,hB,hbound⟩
  have haR : (0:ℝ) ≤ c.a := by exact_mod_cast ha
  have habR : (c.a:ℝ) < c.b := by exact_mod_cast hab
  have hbR : (c.b:ℝ) ≤ 1 := by exact_mod_cast hb
  have hPR : (0:ℝ) < (polynomialBounds c.densityCoeffs c.a c.b).1 := by exact_mod_cast hP
  have hBR : (0:ℝ) ≤ c.bound := by exact_mod_cast hB
  have hpos (s : ℝ) (hs : s ∈ Icc (c.a:ℝ) (c.b:ℝ)) : 0 < eval c.densityCoeffs s :=
    hPR.trans_le (polynomialBounds_sound c.densityCoeffs ha s hs).1
  have hsem := logThirdUnitSum_eq_piece_on_positive_box c.n c.k hn hk haR habR hbR hx
    (fun s hs => by rw [←splineCoeffs_eval,←hp]; exact hpos s hs)
  rw [←hp,←hN] at hsem
  rw [hsem,abs_div,abs_of_pos (pow_pos (hpos x hx) 3)]
  have hNbox := polynomialBounds_sound c.numeratorCoeffs ha x hx
  have hNabs : |eval c.numeratorCoeffs x| ≤
      max |((polynomialBounds c.numeratorCoeffs c.a c.b).1:ℝ)|
        |((polynomialBounds c.numeratorCoeffs c.a c.b).2:ℝ)| := by
    apply abs_le.mpr
    constructor
    · have h := (neg_abs_le ((polynomialBounds c.numeratorCoeffs c.a c.b).1:ℝ)).trans hNbox.1
      have hm := le_max_left |((polynomialBounds c.numeratorCoeffs c.a c.b).1:ℝ)|
        |((polynomialBounds c.numeratorCoeffs c.a c.b).2:ℝ)|
      linarith
    · exact hNbox.2.trans ((le_abs_self _).trans (le_max_right _ _))
  have hbR : max |((polynomialBounds c.numeratorCoeffs c.a c.b).1:ℝ)|
        |((polynomialBounds c.numeratorCoeffs c.a c.b).2:ℝ)| ≤
      (c.bound:ℝ)*((polynomialBounds c.densityCoeffs c.a c.b).1:ℝ)^3 := by exact_mod_cast hbound
  have hpow := pow_le_pow_left₀ hPR.le (polynomialBounds_sound c.densityCoeffs ha x hx).1 3
  apply (div_le_iff₀ (pow_pos (hpos x hx) 3)).mpr
  exact hNabs.trans (hbR.trans (mul_le_mul_of_nonneg_left hpow hBR))

end
end ENT.Small.Quadrature

/-! ## EnclosuresDerivativeGrid -/
/-! Finite exact interval covers for every point of each moving derivative range. -/

@[expose] public section
set_option autoImplicit false
open Set

namespace ENT.Small.Quadrature

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

noncomputable section

theorem DerivativeGrid.cover (g : DerivativeGrid) (hg : g.Valid) (v : ℝ)
    (hv : v ∈ Ioc (g.node 0:ℝ) (g.node g.boxes.length:ℝ)) :
    ∃ i : Fin g.boxes.length,
      v ∈ Ioc (((g.boxes.get i).k:ℝ)+((g.boxes.get i).a:ℝ))
        (((g.boxes.get i).k:ℝ)+((g.boxes.get i).b:ℝ)) := by
  have h := Ioc_subset_biUnion_Ioc g.boxes.length (fun i => (g.node i:ℝ)) hv
  rcases Set.mem_iUnion.mp h with ⟨i,hi⟩
  rcases Set.mem_iUnion.mp hi with ⟨hiN,hit⟩
  let j : Fin g.boxes.length := ⟨i,Finset.mem_range.mp hiN⟩
  have ha : ((g.boxes.get j).k:ℝ)+((g.boxes.get j).a:ℝ) = (g.node j:ℝ) := by
    exact_mod_cast (hg.2 j).2.2.1
  have hb : ((g.boxes.get j).k:ℝ)+((g.boxes.get j).b:ℝ) = (g.node (j+1):ℝ) := by
    exact_mod_cast (hg.2 j).2.2.2
  refine ⟨j,?_⟩
  rw [ha,hb]
  exact hit

theorem ExpandedStep.sound (c : ExpandedStep) (g : DerivativeGrid)
    (hg : g.Valid) (hc : c.Valid g) (v : ℝ)
    (hv : v ∈ Icc ((c.lowerLimit):ℝ) ((c.upperLimit g.n):ℝ)) :
    |logThirdUnitSum g.n v| ≤ (c.bound:ℝ) := by
  rcases hc with ⟨hB,hleft,hright,hbounds⟩
  have hlR : (g.node 0:ℝ) < (c.lowerLimit:ℝ) := by exact_mod_cast hleft
  have hrR : (c.upperLimit g.n:ℝ) ≤ (g.node g.boxes.length:ℝ) := by exact_mod_cast hright
  obtain ⟨i,hi⟩ := g.cover hg v ⟨hlR.trans_le hv.1,hv.2.trans hrR⟩
  have hoverlap : (((g.boxes.get i).k:ℚ)+(g.boxes.get i).a < c.upperLimit g.n) ∧
      (c.lowerLimit ≤ ((g.boxes.get i).k:ℚ)+(g.boxes.get i).b) := by
    constructor
    · exact_mod_cast hi.1.trans_le hv.2
    · exact_mod_cast hv.1.trans hi.2
  have hall : ∀ box ∈ g.boxes,
      (((box.k:ℚ)+box.a < c.upperLimit g.n ∧ c.lowerLimit ≤ (box.k:ℚ)+box.b) →
        box.bound ≤ c.bound) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hbounds
  have hb : ((g.boxes.get i).bound:ℝ) ≤ (c.bound:ℝ) := by
    exact_mod_cast hall (g.boxes.get i) (List.get_mem g.boxes i) hoverlap
  have hx : v-((g.boxes.get i).k:ℝ) ∈
      Icc ((g.boxes.get i).a:ℝ) ((g.boxes.get i).b:ℝ) :=
    ⟨by linarith [hi.1],by linarith [hi.2]⟩
  have h := (g.boxes.get i).sound (hg.2 i).1 _ hx
  rw [show ((g.boxes.get i).k:ℝ)+(v-((g.boxes.get i).k:ℝ))=v by ring,
    (hg.2 i).2.1] at h
  exact h.trans hb

end
end ENT.Small.Quadrature

/-! ## EnclosuresOuterDerivative -/
/-! Exact outer-cell third logarithmic derivatives and singular moving-range envelopes. -/

@[expose] public section
set_option autoImplicit false
open Set

namespace ENT.Small
noncomputable section
open Spline Certificate Quadrature

theorem logThirdUnitSum_five_outer {v : ℝ} (hv : v ∈ Ioc (0:ℝ) 1) :
    logThirdUnitSum 5 v = 8/v^3 := by
  have h := logThirdUnitSum_eq_piece_on_positive_box 5 0 (by decide) (by decide)
    (a:=v/2) (b:=(v+1)/2) (x:=v)
    (by linarith [hv.1]) (by linarith) (by linarith [hv.2])
    ⟨by linarith [hv.1],by linarith [hv.2]⟩ (by
      intro s hs
      have hs0 : 0 < s := by linarith [hv.1,hs.1]
      norm_num [splinePiece,Finset.sum_range_succ]
      positivity)
  have hp : splineCoeffs 5 0 = [0,0,0,0,1] := by decide +kernel
  have hN : logarithmicNumeratorCoeffs [0,0,0,0,1] = [0,0,0,0,0,0,0,0,0,8] := by decide +kernel
  norm_num only [Nat.cast_zero,zero_add,hp,hN] at h
  rw [h]
  norm_num [eval,List.foldr]
  field_simp [hv.1.ne']
  <;> ring

theorem logThirdUnitSum_six_outer {v : ℝ} (hv : v ∈ Ioc (0:ℝ) 1) :
    logThirdUnitSum 6 v = 10/v^3 := by
  have h := logThirdUnitSum_eq_piece_on_positive_box 6 0 (by decide) (by decide)
    (a:=v/2) (b:=(v+1)/2) (x:=v)
    (by linarith [hv.1]) (by linarith) (by linarith [hv.2])
    ⟨by linarith [hv.1],by linarith [hv.2]⟩ (by
      intro s hs
      have hs0 : 0 < s := by linarith [hv.1,hs.1]
      norm_num [splinePiece,Finset.sum_range_succ]
      positivity)
  have hp : splineCoeffs 6 0 = [0,0,0,0,0,1] := by decide +kernel
  have hN : logarithmicNumeratorCoeffs [0,0,0,0,0,1] =
      [0,0,0,0,0,0,0,0,0,0,0,0,10] := by decide +kernel
  norm_num only [Nat.cast_zero,zero_add,hp,hN] at h
  rw [h]
  norm_num [eval,List.foldr]
  field_simp [hv.1.ne']
  <;> ring

theorem outer_moving_bound {n : ℕ} {γ d : ℝ} (hγ : γ ∈ Ico (0:ℝ) 1) (hd : 0 ≤ d)
    (hformula : ∀ v ∈ Ioc (0:ℝ) 1, logThirdUnitSum n v = d/v^3)
    (t : ℝ) (ht : t ∈ Ioc (0:ℝ) (1/2)) (v : ℝ)
    (hv : v ∈ Icc ((1-γ)*t) (min ((n:ℝ)/2) ((1+γ)*t))) :
    |logThirdUnitSum n v| ≤ (d/(1-γ)^3)/t^3 := by
  have hgm : 0 < 1-γ := by linarith [hγ.2]
  have hgp : 0 ≤ 1+γ := by linarith [hγ.1]
  have hv0 : 0 < v := (mul_pos hgm ht.1).trans_le hv.1
  have hv1 : v ≤ 1 := by
    have h := hv.2.trans (min_le_right _ _)
    have hm := mul_le_mul_of_nonneg_left ht.2 hgp
    linarith [hγ.2]
  rw [hformula v ⟨hv0,hv1⟩,abs_of_nonneg (div_nonneg hd (pow_nonneg hv0.le 3))]
  have hp := pow_le_pow_left₀ (mul_pos hgm ht.1).le hv.1 3
  have h := div_le_div_of_nonneg_left hd (pow_pos (mul_pos hgm ht.1) 3) hp
  calc
    d/v^3 ≤ d/((1-γ)*t)^3 := h
    _ = (d/(1-γ)^3)/t^3 := by rw [mul_pow,div_mul_eq_div_div]

end
end ENT.Small

/-! ## QuadratureCube -/
/-! Exact integrals of t³ times the genuine unit-sum spline on one cell. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Small.Quadrature
open Certificate Spline

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

noncomputable section

theorem CubeAreaCertificate.sound (c : CubeAreaCertificate) (hc : c.Valid) :
    (∫ t in ((c.k:ℝ)+(c.a:ℝ))..((c.k:ℝ)+(c.b:ℝ)),
      unitSumSplineDensity c.n t * t^3) = (c.area:ℝ) := by
  rcases hc with ⟨hn,hk,ha,hab,hb,hp,hM,hF,hI⟩
  have haR : (0:ℝ) ≤ c.a := by exact_mod_cast ha
  have habR : (c.a:ℝ) ≤ c.b := by exact_mod_cast hab
  have hbR : (c.b:ℝ) ≤ 1 := by exact_mod_cast hb
  have hcomp := intervalIntegral.integral_comp_add_left
    (f:=fun t : ℝ => unitSumSplineDensity c.n t*t^3)
    (a:=(c.a:ℝ)) (b:=(c.b:ℝ)) (c.k:ℝ)
  rw [←hcomp]
  have he : (∫ t in (c.a:ℝ)..(c.b:ℝ), unitSumSplineDensity c.n ((c.k:ℝ)+t)*((c.k:ℝ)+t)^3) =
      ∫ t in (c.a:ℝ)..(c.b:ℝ),eval c.coeffs t/(Nat.factorial (c.n-1):ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le habR] at ht
    dsimp only
    rw [unitSumSplineDensity,unnormalizedSpline_eq_piece c.n c.k hn hk t
      (haR.trans ht.1) (ht.2.trans hbR),hp,Dense.eval_mul,Dense.eval_power,splineCoeffs_eval]
    simp only [Dense.eval_cons,Dense.eval_nil,Int.cast_natCast,Int.cast_one,mul_zero,add_zero,mul_one]
    ring
  rw [he,intervalIntegral.integral_div,integral_dense_of_primitive hM.ne' hF]
  rw [hI]
  push_cast
  rw [evalRat_cast,evalRat_cast]

end
end ENT.Small.Quadrature
