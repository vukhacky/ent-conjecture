module

public import ENT.Base.TwoDensity
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp

/-! Two crossings of the balanced and unbalanced trapezoid densities for sums of two continuous uniform random variables. -/

@[expose] public section
set_option autoImplicit false
open Set

namespace ENT.Comparison
noncomputable section

def plateauDifference (a c x : ℝ) : ℝ :=
  (2 * c - x) / (4 * c ^ 2) - 1 / (2 * a)

def tailDifference (a b c x : ℝ) : ℝ :=
  (2 * c - x) / (4 * c ^ 2) - (a + b - x) / (4 * a * b)

theorem balancing_width_bounds {a b c : ℝ} (hb : 0 < b) (hab : b < a)
    (hc : 0 < c) (hsq : 2 * c ^ 2 = a ^ 2 + b ^ 2) :
    b < c ∧ c < a ∧ a + b < 2 * c ∧ a * b < c ^ 2 := by
  have ha : 0 < a := hb.trans hab
  have hdiff : 0 < (a - b) ^ 2 := sq_pos_of_pos (sub_pos.mpr hab)
  have habsq : b ^ 2 < a ^ 2 := by nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem plateauDifference_zero_pos {a c : ℝ} (hc : 0 < c) (hca : c < a) :
    0 < plateauDifference a c 0 := by
  have ha : 0 < a := hc.trans hca
  unfold plateauDifference
  have heq : (2 * c - 0) / (4 * c ^ 2) - 1 / (2 * a) =
      (a - c) / (2 * a * c) := by field_simp; ring
  rw [heq]
  positivity

theorem plateauDifference_corner_neg {a b c : ℝ} (hb : 0 < b) (hab : b < a)
    (hc : 0 < c) (hsq : 2 * c ^ 2 = a ^ 2 + b ^ 2) :
    plateauDifference a c (a - b) < 0 := by
  have ha : 0 < a := hb.trans hab
  have hw := balancing_width_bounds hb hab hc hsq
  have hbc : b * c < a ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hab) hc, mul_pos (sub_pos.mpr hw.2.1) ha]
  have hprod : 0 < (a - b) * (a ^ 2 - b * c) := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hbc)
  have hid : (2 * a ^ 2 - a * b + b ^ 2 - 2 * a * c) * (a + c) =
      (a - b) * (a ^ 2 - b * c) := by
    nlinarith [show a * (2 * c ^ 2) = a * (a ^ 2 + b ^ 2) by rw [hsq]]
  have hnum : 0 < 2 * a ^ 2 - a * b + b ^ 2 - 2 * a * c :=
    (mul_pos_iff_of_pos_right (by positivity : 0 < a + c)).mp (hid.symm ▸ hprod)
  have hnum' : a * (2 * c - (a - b)) - 2 * c ^ 2 < 0 := by nlinarith
  unfold plateauDifference
  have heq : (2 * c - (a - b)) / (4 * c ^ 2) - 1 / (2 * a) =
      (a * (2 * c - (a - b)) - 2 * c ^ 2) / (4 * a * c ^ 2) := by
    field_simp
    ring
  rw [heq]
  exact div_neg_of_neg_of_pos hnum' (by positivity)

theorem tailDifference_corner (a b c : ℝ) (hb : b ≠ 0) :
    tailDifference a b c (a - b) = plateauDifference a c (a - b) := by
  unfold tailDifference plateauDifference
  congr 1
  field_simp
  ring

theorem tailDifference_end_pos {a b c : ℝ} (hc : 0 < c) (hwidth : a + b < 2 * c) :
    0 < tailDifference a b c (a + b) := by
  simp only [tailDifference, sub_self, zero_div, sub_zero]
  exact div_pos (sub_pos.mpr hwidth) (by positivity)

theorem antitone_plateauDifference (a c : ℝ) : Antitone (plateauDifference a c) := by
  intro x y hxy
  unfold plateauDifference
  exact sub_le_sub_right (div_le_div_of_nonneg_right (by linarith) (by positivity)) _

theorem monotone_tailDifference {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (habc : a * b ≤ c ^ 2) : Monotone (tailDifference a b c) := by
  intro x y hxy
  have hcoeff : 0 ≤ (c ^ 2 - a * b) / (4 * a * b * c ^ 2) := by positivity
  have heq : tailDifference a b c y - tailDifference a b c x =
      ((c ^ 2 - a * b) / (4 * a * b * c ^ 2)) * (y - x) := by
    unfold tailDifference
    field_simp
    ring
  have hpos : 0 ≤ tailDifference a b c y - tailDifference a b c x := by
    rw [heq]
    exact mul_nonneg hcoeff (sub_nonneg.mpr hxy)
  linarith

theorem exists_two_crossings {a b c : ℝ} (hb : 0 < b) (hab : b < a)
    (hc : 0 < c) (hsq : 2 * c ^ 2 = a ^ 2 + b ^ 2) :
    ∃ r ∈ Ioo 0 (a - b), ∃ s ∈ Ioo (a - b) (a + b),
      plateauDifference a c r = 0 ∧ tailDifference a b c s = 0 := by
  have hw := balancing_width_bounds hb hab hc hsq
  have hneg := plateauDifference_corner_neg hb hab hc hsq
  have hzero := plateauDifference_zero_pos hc hw.2.1
  have hpcont : Continuous (plateauDifference a c) := by unfold plateauDifference; fun_prop
  have htcont : Continuous (tailDifference a b c) := by unfold tailDifference; fun_prop
  obtain ⟨r, hr, hroot⟩ := intermediate_value_Ioo' (by linarith : 0 ≤ a - b)
    hpcont.continuousOn ⟨hneg, hzero⟩
  have htailneg : tailDifference a b c (a - b) < 0 := by
    rw [tailDifference_corner a b c hb.ne']
    exact hneg
  obtain ⟨s, hs, hroot'⟩ := intermediate_value_Ioo (by linarith : a - b ≤ a + b)
    htcont.continuousOn ⟨htailneg, tailDifference_end_pos hc hw.2.2.1⟩
  exact ⟨r, hr, s, hs, hroot, hroot'⟩

theorem twoDensity_balanced_eq {c x : ℝ} (hc : 0 < c)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * c) :
    twoDensity c c x = (2 * c - x) / (4 * c ^ 2) := by
  rw [twoDensity_eq_slope le_rfl (by linarith) (by linarith)]
  field_simp
  ring

theorem density_difference_plateau {a b c x : ℝ} (hb : 0 < b) (hab : b ≤ a)
    (hc : 0 < c) (hx0 : 0 ≤ x) (hxd : x ≤ a - b) (hxR : x ≤ 2 * c) :
    twoDensity c c x - twoDensity a b x = plateauDifference a c x := by
  rw [twoDensity_eq_const hb hab hx0 hxd, twoDensity_balanced_eq hc hx0 hxR]
  simp only [plateauDifference, one_div]

theorem density_difference_tail {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ a) (hc : 0 < c) (hxd : a - b ≤ x) (hxA : x ≤ a + b)
    (hxR : x ≤ 2 * c) :
    twoDensity c c x - twoDensity a b x = tailDifference a b c x := by
  rw [twoDensity_eq_slope hab hxd hxA, twoDensity_balanced_eq hc (by linarith) hxR]
  unfold tailDifference
  field_simp
  ring

/-- The balanced density minus the unbalanced density has sign +,-,+ on the
positive half line, with two strict interior crossing locations. -/
theorem twoDensity_balance_crossing_signs {a b c : ℝ} (hb : 0 < b) (hab : b < a)
    (hc : 0 < c) (hsq : 2 * c ^ 2 = a ^ 2 + b ^ 2) :
    ∃ r ∈ Ioo 0 (a - b), ∃ s ∈ Ioo (a - b) (a + b),
      (∀ x, 0 ≤ x → (x ≤ r ∨ s ≤ x) → 0 ≤ twoDensity c c x - twoDensity a b x) ∧
      (∀ x, r ≤ x → x ≤ s → twoDensity c c x - twoDensity a b x ≤ 0) := by
  have ha : 0 < a := hb.trans hab
  have hw := balancing_width_bounds hb hab hc hsq
  obtain ⟨r, hr, s, hs, hroot, hroot'⟩ := exists_two_crossings hb hab hc hsq
  have hanti := antitone_plateauDifference a c
  have hmono := monotone_tailDifference ha hb hc hw.2.2.2.le
  refine ⟨r, hr, s, hs, ?_, ?_⟩
  · intro x hx0 hx
    rcases hx with hx | hx
    · rw [density_difference_plateau hb hab.le hc hx0 (by linarith [hr.2])
        (by linarith [hr.2, hw.2.2.1])]
      rw [← hroot]
      exact hanti hx
    · by_cases hxA : x ≤ a + b
      · rw [density_difference_tail ha hb hab.le hc (by linarith [hs.1]) hxA
          (hxA.trans hw.2.2.1.le)]
        rw [← hroot']
        exact hmono hx
      · have hz := twoDensity_eq_zero_of_not_mem a b x (by
          intro hmem
          exact hxA hmem.2)
        rw [hz, sub_zero]
        exact twoDensity_nonneg hc hc x
  · intro x hxr hxs
    have hx0 : 0 ≤ x := le_trans hr.1.le hxr
    have hxA : x ≤ a + b := le_trans hxs hs.2.le
    by_cases hxd : x ≤ a - b
    · rw [density_difference_plateau hb hab.le hc hx0 hxd (hxA.trans hw.2.2.1.le)]
      rw [← hroot]
      exact hanti hxr
    · rw [density_difference_tail ha hb hab.le hc (le_of_not_ge hxd) hxA
        (hxA.trans hw.2.2.1.le)]
      rw [← hroot']
      exact hmono hxs

end
end ENT.Comparison
