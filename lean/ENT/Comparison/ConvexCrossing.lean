module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Two crossings and equal first moments imply convex order by comparison with the secant line. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Comparison
noncomputable section

def secantLine (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ((b - x) * f a + (x - a) * f b) / (b - a)

theorem secantLine_affine (f : ℝ → ℝ) (a b x : ℝ) :
    secantLine f a b x = (b * f a - a * f b) / (b - a) +
      ((f b - f a) / (b - a)) * x := by
  unfold secantLine
  ring

theorem convex_le_secant {f : ℝ → ℝ} {D : Set ℝ} (hf : ConvexOn ℝ D f)
    {a b x : ℝ} (ha : a ∈ D) (hb : b ∈ D) (hab : a < b)
    (hax : a ≤ x) (hxb : x ≤ b) : f x ≤ secantLine f a b x := by
  rcases eq_or_lt_of_le hax with hax | hax
  · subst x
    simp [secantLine, (sub_pos.mpr hab).ne']
  rcases eq_or_lt_of_le hxb with hxb | hxb
  · subst x
    simp [secantLine, (sub_pos.mpr hab).ne']
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  have h := hf.secant_mono_aux1 ha hb hax hxb
  nlinarith

theorem secant_le_convex_left {f : ℝ → ℝ} {D : Set ℝ} (hf : ConvexOn ℝ D f)
    {a b x : ℝ} (hx : x ∈ D) (hb : b ∈ D) (hab : a < b)
    (hxa : x ≤ a) : secantLine f a b x ≤ f x := by
  rcases eq_or_lt_of_le hxa with hxa | hxa
  · subst x
    simp [secantLine, (sub_pos.mpr hab).ne']
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have h := hf.secant_mono_aux1 hx hb hxa hab
  nlinarith

theorem secant_le_convex_right {f : ℝ → ℝ} {D : Set ℝ} (hf : ConvexOn ℝ D f)
    {a b x : ℝ} (ha : a ∈ D) (hx : x ∈ D) (hab : a < b)
    (hbx : b ≤ x) : secantLine f a b x ≤ f x := by
  rcases eq_or_lt_of_le hbx with hbx | hbx
  · subst x
    simp [secantLine, (sub_pos.mpr hab).ne']
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have h := hf.secant_mono_aux1 ha hx hab hbx
  nlinarith

theorem integral_nonneg_of_affine_sign {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d X F : Ω → ℝ} (hd : Integrable d μ)
    (hXd : Integrable (fun x => X x * d x) μ)
    (hFd : Integrable (fun x => F x * d x) μ)
    (hmass : (∫ x, d x ∂μ) = 0) (hmean : (∫ x, X x * d x ∂μ) = 0)
    (u v : ℝ) (hsign : ∀ᵐ x ∂μ, 0 ≤ (F x - (u + v * X x)) * d x) :
    0 ≤ ∫ x, F x * d x ∂μ := by
  have hlin : Integrable (fun x => (u + v * X x) * d x) μ := by
    have h := (hd.const_mul u).add (hXd.const_mul v)
    convert h using 1 <;> ext x <;> simp only [Pi.add_apply] <;> ring
  have hzero : (∫ x, (u + v * X x) * d x ∂μ) = 0 := by
    have heq : (fun x => (u + v * X x) * d x) =
        (fun x => u * d x + v * (X x * d x)) := by funext x; ring
    rw [heq, integral_add (hd.const_mul u) (hXd.const_mul v),
      integral_const_mul, integral_const_mul, hmass, hmean]
    ring
  have hnonneg := integral_nonneg_of_ae hsign
  have heq : (fun x => (F x - (u + v * X x)) * d x) =
      (fun x => F x * d x - (u + v * X x) * d x) := by funext x; ring
  rw [heq, integral_sub hFd hlin, hzero, sub_zero] at hnonneg
  exact hnonneg

/-- A signed density with zero mass and first moment, positive outside the
two crossings and negative between them, has nonnegative integral against
every integrable convex test function. -/
theorem integral_convex_nonneg_of_two_crossings_support {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d X : Ω → ℝ} {f : ℝ → ℝ} {D : Set ℝ}
    (hf : ConvexOn ℝ D f) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (hab : a < b)
    (hX : ∀ᵐ x ∂μ, d x ≠ 0 → X x ∈ D)
    (hd : Integrable d μ) (hXd : Integrable (fun x => X x * d x) μ)
    (hfd : Integrable (fun x => f (X x) * d x) μ)
    (hmass : (∫ x, d x ∂μ) = 0) (hmean : (∫ x, X x * d x ∂μ) = 0)
    (houtside : ∀ᵐ x ∂μ, X x ≤ a ∨ b ≤ X x → 0 ≤ d x)
    (hinside : ∀ᵐ x ∂μ, a ≤ X x ∧ X x ≤ b → d x ≤ 0) :
    0 ≤ ∫ x, f (X x) * d x ∂μ := by
  apply integral_nonneg_of_affine_sign hd hXd hfd hmass hmean
    ((b * f a - a * f b) / (b - a)) ((f b - f a) / (b - a))
  filter_upwards [hX, houtside, hinside] with x hx' hout hin
  by_cases hz : d x = 0
  · simp only [hz, mul_zero, le_refl]
  have hx := hx' hz
  rw [← secantLine_affine]
  rcases le_total (X x) a with hleft | hleft
  · exact mul_nonneg (sub_nonneg.mpr (secant_le_convex_left hf hx hb hab hleft))
      (hout (Or.inl hleft))
  rcases le_total b (X x) with hright | hright
  · exact mul_nonneg (sub_nonneg.mpr (secant_le_convex_right hf ha hx hab hright))
      (hout (Or.inr hright))
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (convex_le_secant hf ha hb hab hleft hright)) (hin ⟨hleft, hright⟩)

theorem integral_convex_nonneg_of_two_crossings {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d X : Ω → ℝ} {f : ℝ → ℝ} {D : Set ℝ}
    (hf : ConvexOn ℝ D f) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (hab : a < b)
    (hX : ∀ᵐ x ∂μ, X x ∈ D)
    (hd : Integrable d μ) (hXd : Integrable (fun x => X x * d x) μ)
    (hfd : Integrable (fun x => f (X x) * d x) μ)
    (hmass : (∫ x, d x ∂μ) = 0) (hmean : (∫ x, X x * d x ∂μ) = 0)
    (houtside : ∀ᵐ x ∂μ, X x ≤ a ∨ b ≤ X x → 0 ≤ d x)
    (hinside : ∀ᵐ x ∂μ, a ≤ X x ∧ X x ≤ b → d x ≤ 0) :
    0 ≤ ∫ x, f (X x) * d x ∂μ :=
  integral_convex_nonneg_of_two_crossings_support hf ha hb hab
    (hX.mono fun _ hx _ => hx) hd hXd hfd hmass hmean houtside hinside

end
end ENT.Comparison
