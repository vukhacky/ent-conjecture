module

public import ENT.Comparison.UniformAverage
public import ENT.Comparison.TwoExpectation

/-!
A local analytic class preserved by averaging independent uniform variables.
The first two derivative functions have continuous global extensions; their
derivative identities are required only on the stated open interval. Convexity
of the first derivative is encoded by monotonicity of the second derivative.
-/

@[expose] public section
set_option autoImplicit false
open Set

namespace ENT.Comparison
noncomputable section

structure EvenJet (R : ℝ) (g : ℝ → ℝ) where
  radius_pos : 0 < R
  first : ℝ → ℝ
  second : ℝ → ℝ
  continuous : Continuous g
  first_continuous : Continuous first
  second_continuous : Continuous second
  even : ∀ x, g (-x) = g x
  first_odd : ∀ x, first (-x) = -first x
  second_even : ∀ x, second (-x) = second x
  hasDeriv : ∀ x ∈ Ioo (-R) R, HasDerivAt g (first x) x
  hasDeriv_first : ∀ x ∈ Ioo (-R) R, HasDerivAt first (second x) x
  second_mono : MonotoneOn second (Icc 0 R)

theorem uniformDifference_odd {g : ℝ → ℝ} (heven : ∀ x, g (-x) = g x)
    (b x : ℝ) : uniformDifference b g (-x) = -uniformDifference b g x := by
  unfold uniformDifference
  rw [show -x + b = -(x - b) by ring, show -x - b = -(x + b) by ring, heven, heven]
  ring

theorem uniformDifference_even {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = -g x)
    (b x : ℝ) : uniformDifference b g (-x) = uniformDifference b g x := by
  unfold uniformDifference
  rw [show -x + b = -(x - b) by ring, show -x - b = -(x + b) by ring, hodd, hodd]
  ring

theorem uniformDifference_nonneg {g : ℝ → ℝ} {R b x : ℝ}
    (heven : ∀ x, g (-x) = g x) (hmono : MonotoneOn g (Icc 0 R))
    (hb : 0 ≤ b) (hx : 0 ≤ x) (hR : x + b ≤ R) :
    0 ≤ uniformDifference b g x := by
  have habs : |x - b| ≤ x + b := (abs_le).mpr ⟨by linarith, by linarith⟩
  have hg := hmono ⟨abs_nonneg _, habs.trans hR⟩ ⟨by positivity, hR⟩ habs
  rw [even_apply_abs heven] at hg
  exact div_nonneg (sub_nonneg.mpr hg) (by positivity)

theorem shifted_mem_Ioo {R b x : ℝ} (hb : 0 ≤ b) (hx : x ∈ Ioo (-(R - b)) (R - b)) :
    x + b ∈ Ioo (-R) R ∧ x - b ∈ Ioo (-R) R := by
  constructor <;> constructor <;> linarith [hx.1, hx.2]

namespace EvenJet

variable {R : ℝ} {g : ℝ → ℝ}

theorem first_zero (J : EvenJet R g) : J.first 0 = 0 := by
  have h := J.first_odd 0
  simp only [neg_zero] at h
  linarith

theorem first_convex (J : EvenJet R g) : ConvexOn ℝ (Icc 0 R) J.first := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 R) J.first_continuous.continuousOn
  · rw [interior_Icc]
    intro x hx
    exact (J.hasDeriv_first x ⟨by linarith [J.radius_pos, hx.1], hx.2⟩).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    rw [(J.hasDeriv_first x ⟨by linarith [J.radius_pos, hx.1], hx.2⟩).deriv,
      (J.hasDeriv_first y ⟨by linarith [J.radius_pos, hy.1], hy.2⟩).deriv]
    exact J.second_mono ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy

theorem square_convex (J : EvenJet R g) :
    ConvexOn ℝ (Icc 0 (R ^ 2)) (fun x => g (Real.sqrt x)) := by
  apply convex_sqrt_comp_of_convex_derivative J.radius_pos J.continuous.continuousOn
    (fun x hx => J.hasDeriv x ⟨by linarith [J.radius_pos, hx.1], hx.2⟩)
    J.first_convex J.first_zero

/-- One uniform average preserves the analytic class on the reduced interval.
The norm bound guarantees continuity of the probability integral globally. -/
def average (J : EvenJet R g) {b C : ℝ} (hb : 0 < b) (hbR : b < R)
    (hC : ∀ x, ‖g x‖ ≤ C) : EvenJet (R - b) (uniformAverage b g) where
  radius_pos := sub_pos.mpr hbR
  first := uniformDifference b g
  second := uniformDifference b J.first
  continuous := continuous_uniformAverage J.continuous hC b
  first_continuous := continuous_uniformDifference J.continuous b
  second_continuous := continuous_uniformDifference J.first_continuous b
  even := uniformAverage_even J.continuous J.even b
  first_odd := uniformDifference_odd J.even b
  second_even := uniformDifference_even J.first_odd b
  hasDeriv := fun x _ => hasDerivAt_uniformAverage hb J.continuous x
  hasDeriv_first := by
    intro x hx
    have hshift := shifted_mem_Ioo hb.le hx
    exact hasDerivAt_uniformDifference (J.hasDeriv (x + b) hshift.1)
      (J.hasDeriv (x - b) hshift.2)
  second_mono := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (R - b))
      (continuous_uniformDifference J.first_continuous b).continuousOn
      (f' := uniformDifference b J.second)
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Ioo (-(R - b)) (R - b) := ⟨by linarith [hx.1], hx.2⟩
      have hshift := shifted_mem_Ioo hb.le hx'
      exact (hasDerivAt_uniformDifference (J.hasDeriv_first (x + b) hshift.1)
        (J.hasDeriv_first (x - b) hshift.2)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact uniformDifference_nonneg J.second_even J.second_mono hb.le hx.1.le (by linarith [hx.2])

theorem pair_comparison (J : EvenJet R g) {a b c C : ℝ}
    (hb : 0 ≤ b) (hab : b ≤ a) (hc : 0 < c)
    (hsq : 2 * c ^ 2 = a ^ 2 + b ^ 2) (hR : 2 * c ≤ R)
    (hC : ∀ x, ‖g x‖ ≤ C) :
    potentialExpectation g ![a, b] ≤ potentialExpectation g ![c, c] := by
  apply two_expectation_balancing hb hab hc hsq J.continuous hC J.even
  apply J.square_convex.subset _ (convex_Icc 0 ((2 * c) ^ 2))
  intro x hx
  exact ⟨hx.1, le_trans hx.2 (by nlinarith [J.radius_pos])⟩

end EvenJet
end
end ENT.Comparison
