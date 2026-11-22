module

public import ENT.Comparison.ConvexCrossing
public import ENT.Comparison.TwoDensityCrossings
public import ENT.Comparison.TwoMoments
public import ENT.Comparison.SquareConvex

/-! Convex order of squared two-uniform sums, proved from actual densities,
their equal second moments, and the exact two-crossing geometry. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Comparison
noncomputable section

theorem twoDensity_abs (a b x : ℝ) : twoDensity a b |x| = twoDensity a b x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, twoDensity_neg]

theorem square_mem_Icc {R x : ℝ} (hR : 0 ≤ R) (hx : x ∈ Icc (-R) R) :
    x ^ 2 ∈ Icc 0 (R ^ 2) := by
  refine ⟨sq_nonneg x, ?_⟩
  have hprod := mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.1] : 0 ≤ R + x)
  nlinarith

theorem twoDensity_convex_square_le {a b c : ℝ} (hb : 0 < b) (hab : b < a)
    (hc : 0 < c) (hsq : 2 * c ^ 2 = a ^ 2 + b ^ 2)
    {φ : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc 0 ((2 * c) ^ 2)))
    (hφconv : ConvexOn ℝ (Icc 0 ((2 * c) ^ 2)) φ) :
    (∫ x, φ (x ^ 2) * twoDensity a b x) ≤
      ∫ x, φ (x ^ 2) * twoDensity c c x := by
  have ha : 0 < a := hb.trans hab
  have hw := balancing_width_bounds hb hab hc hsq
  have hlarge : Icc (-(a + b)) (a + b) ⊆ Icc (-(2 * c)) (2 * c) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2, hw.2.2.1]
  have hg : ContinuousOn (fun x => φ (x ^ 2)) (Icc (-(2 * c)) (2 * c)) :=
    hφcont.comp (continuous_id.pow 2).continuousOn
      (fun _ hx => square_mem_Icc (by positivity) hx)
  have hgp : Integrable (fun x => φ (x ^ 2) * twoDensity a b x) volume :=
    integrable_mul_twoDensity (hg.mono hlarge)
  have hgq : Integrable (fun x => φ (x ^ 2) * twoDensity c c x) volume :=
    integrable_mul_twoDensity (by simpa only [two_mul] using hg)
  have hp : Integrable (twoDensity a b) volume := (twoFiniteEntropyDensity ![a, b] ha hb).integrable
  have hq : Integrable (twoDensity c c) volume := (twoFiniteEntropyDensity ![c, c] hc hc).integrable
  have hmp : Integrable (fun x => x ^ 2 * twoDensity a b x) volume :=
    integrable_mul_twoDensity (continuous_id.pow 2).continuousOn
  have hmq : Integrable (fun x => x ^ 2 * twoDensity c c x) volume :=
    integrable_mul_twoDensity (continuous_id.pow 2).continuousOn
  obtain ⟨r, hr, s, hs, hout, hin⟩ := twoDensity_balance_crossing_signs hb hab hc hsq
  have hr0 : 0 < r := hr.1
  have hrs : r < s := hr.2.trans hs.1
  have hsR : s < 2 * c := hs.2.trans hw.2.2.1
  have hrD : r ^ 2 ∈ Icc 0 ((2 * c) ^ 2) := by
    apply square_mem_Icc (by positivity)
    constructor <;> linarith
  have hsD : s ^ 2 ∈ Icc 0 ((2 * c) ^ 2) := by
    apply square_mem_Icc (by positivity)
    constructor <;> linarith
  have hrs2 : r ^ 2 < s ^ 2 := by nlinarith
  have hnonneg : 0 ≤ ∫ x, φ (x ^ 2) * (twoDensity c c x - twoDensity a b x) := by
    apply integral_convex_nonneg_of_two_crossings_support hφconv hrD hsD hrs2
      (X := fun x : ℝ => x ^ 2) (d := fun x => twoDensity c c x - twoDensity a b x)
    · apply Filter.Eventually.of_forall
      intro x hne
      by_cases hx : x ∈ Icc (-(2 * c)) (2 * c)
      · exact square_mem_Icc (by positivity) hx
      · have hzp : twoDensity a b x = 0 := twoDensity_eq_zero_of_not_mem a b x
          (fun h => hx (hlarge h))
        have hzq : twoDensity c c x = 0 := twoDensity_eq_zero_of_not_mem c c x
          (by simpa only [two_mul] using hx)
        exact False.elim (hne (by rw [hzp, hzq, sub_self]))
    · exact hq.sub' hp
    · simpa only [mul_sub] using hmq.sub' hmp
    · simpa only [mul_sub] using hgq.sub' hgp
    · rw [integral_sub hq hp, integral_twoDensity hc hc, integral_twoDensity ha hb, sub_self]
    · simp_rw [mul_sub]
      rw [integral_sub hmq hmp, integral_twoDensity_second hc hc le_rfl,
        integral_twoDensity_second ha hb hab.le]
      linarith
    · apply Filter.Eventually.of_forall
      intro x hx
      rw [← twoDensity_abs c c x, ← twoDensity_abs a b x]
      apply hout |x| (abs_nonneg x)
      rcases hx with hx | hx
      · left
        nlinarith [sq_abs x, abs_nonneg x]
      · right
        nlinarith [sq_abs x, abs_nonneg x]
    · apply Filter.Eventually.of_forall
      intro x hx
      rw [← twoDensity_abs c c x, ← twoDensity_abs a b x]
      apply hin |x|
      · nlinarith [sq_abs x, abs_nonneg x, hx.1]
      · nlinarith [sq_abs x, abs_nonneg x, hx.2]
  simp_rw [mul_sub] at hnonneg
  rw [integral_sub hgq hgp] at hnonneg
  linarith

end
end ENT.Comparison
