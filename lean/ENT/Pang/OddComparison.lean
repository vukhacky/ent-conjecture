module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The single-crossing odd-convex comparison

This is the comparison behind Pang's signed sine estimates. It uses the
actual zero first moment, not symmetry. The density may have a nonzero odd
part, with one sign change on the positive half-line.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

/-- Subtracting the chord through zero and the crossing point makes the
product with the odd part of the density nonpositive everywhere. -/
theorem odd_convex_chord_product_nonpos {f h : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hodd : ∀ x, h (-x) = -h x)
    (hconv : ConvexOn ℝ (Ici 0) h)
    (hleft : ∀ x, 0 < x → x < b → 0 ≤ f x - f (-x))
    (hright : ∀ x, b < x → f x - f (-x) ≤ 0) (x : ℝ) :
    (h x - h b / b * x) * (f x - f (-x)) ≤ 0 := by
  have hzero : h 0 = 0 := by
    have hz := hodd 0
    simp only [neg_zero] at hz
    linarith
  have hpos : ∀ x : ℝ, 0 ≤ x →
      (h x - h b / b * x) * (f x - f (-x)) ≤ 0 := by
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hx
    · simp [hzero]
    rcases lt_trichotomy x b with hxb | rfl | hbx
    · have hs : h x / x ≤ h b / b := by
        simpa only [hzero, sub_zero] using
          hconv.secant_mono (show (0 : ℝ) ∈ Ici 0 from le_rfl)
            hx.le hb.le hx.ne' hb.ne' hxb.le
      have hc : h x - h b / b * x ≤ 0 := by
        exact sub_nonpos.mpr ((div_le_iff₀ hx).mp hs)
      exact mul_nonpos_of_nonpos_of_nonneg hc (hleft x hx hxb)
    · have hc : h x - h x / x * x = 0 := by field_simp; ring
      rw [hc, zero_mul]
    · have hs : h b / b ≤ h x / x := by
        simpa only [hzero, sub_zero] using
          hconv.secant_mono (show (0 : ℝ) ∈ Ici 0 from le_rfl)
            hb.le hx.le hb.ne' hx.ne' hbx.le
      have hc : 0 ≤ h x - h b / b * x := by
        exact sub_nonneg.mpr ((le_div_iff₀ hx).mp hs)
      exact mul_nonpos_of_nonneg_of_nonpos hc (hright x hbx)
  by_cases hx : 0 ≤ x
  · exact hpos x hx
  · have hp := hpos (-x) (by linarith)
    have heq : (h (-x) - h b / b * (-x)) * (f (-x) - f (-(-x))) =
        (h x - h b / b * x) * (f x - f (-x)) := by
      rw [hodd, neg_neg]
      ring
    rwa [heq] at hp

/-- A centered single-crossing density has nonpositive expectation against
every integrable odd function that is convex on the positive half-line. -/
theorem integral_odd_convex_nonpos {f h : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hodd : ∀ x, h (-x) = -h x)
    (hconv : ConvexOn ℝ (Ici 0) h)
    (hleft : ∀ x, 0 < x → x < b → 0 ≤ f x - f (-x))
    (hright : ∀ x, b < x → f x - f (-x) ≤ 0)
    (hhf : Integrable (fun x => h x * f x))
    (hxf : Integrable (fun x => x * f x))
    (hmean : (∫ x, x * f x) = 0) :
    (∫ x, h x * f x) ≤ 0 := by
  have hr : Integrable (fun x => (h x - h b / b * x) * f x) := by
    apply (hhf.sub (hxf.const_mul (h b / b))).congr
    exact Filter.Eventually.of_forall (fun x => by dsimp; ring)
  have heq : (fun x => (h x - h b / b * x) * (f x - f (-x))) =
      (fun x => (h x - h b / b * x) * f x +
        (h (-x) - h b / b * (-x)) * f (-x)) := by
    funext x
    rw [hodd]
    ring
  have hint : (∫ x, (h x - h b / b * x) * f x) = ∫ x, h x * f x := by
    have he : (fun x => (h x - h b / b * x) * f x) =
        (fun x => h x * f x - h b / b * (x * f x)) := by
      funext x
      ring
    rw [he, integral_sub hhf (hxf.const_mul _), integral_const_mul, hmean]
    ring
  have hnonpos : (∫ x, (h x - h b / b * x) * (f x - f (-x))) ≤ 0 :=
    integral_nonpos (odd_convex_chord_product_nonpos hb hodd hconv hleft hright)
  have hrneg : Integrable (fun x => (h (-x) - h b / b * (-x)) * f (-x)) := by
    simpa only [neg_one_mul] using hr.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
  have hineg : (∫ x, (h (-x) - h b / b * (-x)) * f (-x)) =
      ∫ x, (h x - h b / b * x) * f x := by
    simpa using Measure.integral_comp_mul_left
      (fun x => (h x - h b / b * x) * f x) (-1 : ℝ)
  rw [heq, integral_add hr hrneg, hineg, hint] at hnonpos
  linarith

end
end ENT.Pang
