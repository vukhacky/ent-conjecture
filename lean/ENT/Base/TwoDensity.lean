module

public import ENT.Basic.Independence
public import ENT.Basic.ScaledUniform
public import ENT.Basic.Symmetry
public import ENT.Entropy.Finite
public import ENT.Entropy.LawInvariance
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
The actual convolution density for two positive uniform summands.  The formula
uses the length of the intersection of two intervals; its connection with the
canonical product law is proved, rather than assumed.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ENT

noncomputable section

def twoDensity (a b x : ℝ) : ℝ :=
  ((2 * a)⁻¹ * (2 * b)⁻¹) * max 0 (min a (x + b) - max (-a) (x - b))

theorem continuous_twoDensity (a b : ℝ) : Continuous (twoDensity a b) := by
  unfold twoDensity
  fun_prop

theorem twoDensity_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ twoDensity a b x := by
  unfold twoDensity
  positivity

theorem twoDensity_neg (a b x : ℝ) : twoDensity a b (-x) = twoDensity a b x := by
  have hmin : min a (-x + b) = -max (-a) (x - b) := by
    rw [← min_neg_neg, neg_neg]
    congr 1
    ring
  have hmax : max (-a) (-x - b) = -min a (x + b) := by
    rw [← max_neg_neg]
    congr 1
    ring
  have hlen : min a (-x + b) - max (-a) (-x - b) =
      min a (x + b) - max (-a) (x - b) := by
    rw [hmin, hmax]
    ring
  simp only [twoDensity, hlen]

theorem twoDensity_eq_const {a b x : ℝ} (hb : 0 < b) (hab : b ≤ a)
    (hx0 : 0 ≤ x) (hx1 : x ≤ a - b) : twoDensity a b x = (2 * a)⁻¹ := by
  rw [twoDensity, min_eq_right (by linarith : x + b ≤ a),
    max_eq_right (by linarith : -a ≤ x - b)]
  rw [show x + b - (x - b) = 2 * b by ring,
    max_eq_right (by positivity : 0 ≤ 2 * b), mul_assoc,
    inv_mul_cancel₀ (by positivity : 2 * b ≠ 0), mul_one]

theorem twoDensity_eq_slope {a b x : ℝ} (hab : b ≤ a)
    (hx0 : a - b ≤ x) (hx1 : x ≤ a + b) :
    twoDensity a b x = ((2 * a)⁻¹ * (2 * b)⁻¹) * (a + b - x) := by
  rw [twoDensity, min_eq_left (by linarith : a ≤ x + b),
    max_eq_right (by linarith : -a ≤ x - b)]
  rw [show a - (x - b) = a + b - x by ring, max_eq_right (by linarith)]

theorem twoDensity_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    twoDensity a b x ≤ ((2 * a)⁻¹ * (2 * b)⁻¹) * (2 * a) := by
  have hlen : min a (x + b) - max (-a) (x - b) ≤ 2 * a := by
    linarith [min_le_left a (x + b), le_max_left (-a) (x - b)]
  exact mul_le_mul_of_nonneg_left (max_le (by linarith) hlen) (by positivity)

theorem twoDensity_eq_zero_of_not_mem (a b x : ℝ)
    (hx : x ∉ Set.Icc (-(a + b)) (a + b)) : twoDensity a b x = 0 := by
  have hx' : x < -(a + b) ∨ a + b < x := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  have hlen : min a (x + b) - max (-a) (x - b) ≤ 0 := by
    rcases hx' with hx' | hx'
    · linarith [min_le_right a (x + b), le_max_left (-a) (x - b)]
    · linarith [min_le_left a (x + b), le_max_right (-a) (x - b)]
  simp only [twoDensity, max_eq_left hlen, mul_zero]

theorem scaledUniformDensity_lconvolution {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x : ℝ) :
    lconvolution (fun y => ENNReal.ofReal (scaledUniformDensity a y))
      (fun y => ENNReal.ofReal (scaledUniformDensity b y)) volume x =
      ENNReal.ofReal (twoDensity a b x) := by
  have hfun : (fun y => ENNReal.ofReal (scaledUniformDensity a y) *
      ENNReal.ofReal (scaledUniformDensity b (-y + x))) =
      (Set.Icc (max (-a) (x - b)) (min a (x + b))).indicator
        (fun _ : ℝ => ENNReal.ofReal ((2 * a)⁻¹) * ENNReal.ofReal ((2 * b)⁻¹)) := by
    funext y
    have hmem : y ∈ Set.Icc (max (-a) (x - b)) (min a (x + b)) ↔
        y ∈ Set.Icc (-a) a ∧ -y + x ∈ Set.Icc (-b) b := by
      simp only [Set.mem_Icc, max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
        exact ⟨⟨h₁, h₃⟩, ⟨by linarith, by linarith⟩⟩
      · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
        exact ⟨⟨h₁, by linarith⟩, ⟨h₂, by linarith⟩⟩
    by_cases hya : y ∈ Set.Icc (-a) a <;>
      by_cases hyb : -y + x ∈ Set.Icc (-b) b <;>
      simp [scaledUniformDensity, Set.indicator, hmem, hya, hyb]
  rw [lconvolution_def, hfun, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
  rw [twoDensity, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  simp

theorem twoDensity_law (a : Fin 2 → ℝ) (ha : 0 < a 0) (hb : 0 < a 1) :
    projectionLaw a =
      volume.withDensity (fun x => ENNReal.ofReal (twoDensity (a 0) (a 1) x)) := by
  rw [projectionLaw_two_eq_conv, scaledUniformDensity_law ha, scaledUniformDensity_law hb,
    conv_withDensity_eq_lconvolution
      (measurable_scaledUniformDensity (a 0)).ennreal_ofReal
      (measurable_scaledUniformDensity (a 1)).ennreal_ofReal]
  congr 1
  funext x
  exact scaledUniformDensity_lconvolution ha hb x

def twoFiniteEntropyDensity (a : Fin 2 → ℝ) (ha : 0 < a 0) (hb : 0 < a 1) :
    FiniteEntropyDensity (projectionLaw a) :=
  finiteEntropyDensityOfBoundedSupportLaw (projectionLaw a) (twoDensity (a 0) (a 1))
    (((2 * a 0)⁻¹ * (2 * a 1)⁻¹) * (2 * a 0)) (a 0 + a 1)
    (continuous_twoDensity (a 0) (a 1)).measurable
    (twoDensity_nonneg ha hb) (twoDensity_le ha hb)
    (twoDensity_eq_zero_of_not_mem (a 0) (a 1)) (twoDensity_law a ha hb)

end
end ENT
