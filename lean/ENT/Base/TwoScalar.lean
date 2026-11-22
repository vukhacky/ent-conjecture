module

public import ENT.Statement
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Exact scalar entropy gap for the two-coordinate parametrization. -/

set_option autoImplicit false

@[expose] public section

namespace ENT

noncomputable section

def twoGap (r : ℝ) : ℝ :=
  (1 - r + Real.log ((1 + r ^ 2) / 2)) / 2

@[simp]
theorem twoGap_one : twoGap 1 = 0 := by
  norm_num [twoGap]

theorem hasDerivAt_twoGap (r : ℝ) :
    HasDerivAt twoGap (-(1 - r) ^ 2 / (2 * (1 + r ^ 2))) r := by
  have hpos : 0 < 1 + r ^ 2 := by positivity
  have harg : (1 + r ^ 2) / 2 ≠ 0 := ne_of_gt (div_pos hpos (by norm_num))
  have hlog := ((((hasDerivAt_id r).pow 2).const_add 1).div_const 2).log harg
  have hraw := (((hasDerivAt_id r).const_sub 1).add hlog).div_const 2
  simp only [Pi.pow_apply, Pi.add_apply, id_eq] at hraw
  unfold twoGap
  convert hraw using 1
  field_simp [hpos.ne']
  ring

theorem strictAntiOn_twoGap : StrictAntiOn twoGap (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · have hcont : Continuous twoGap :=
      continuous_iff_continuousAt.mpr fun r => (hasDerivAt_twoGap r).continuousAt
    exact hcont.continuousOn
  · intro r hr
    rw [interior_Icc] at hr
    rw [(hasDerivAt_twoGap r).deriv]
    have hnum : 0 < (1 - r) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr.2)
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) (by positivity)

theorem twoGap_pos {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : 0 < twoGap r := by
  have h := strictAntiOn_twoGap ⟨h0, h1.le⟩ ⟨by norm_num, le_rfl⟩ h1
  simpa using h

theorem twoGap_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ twoGap r := by
  rcases lt_or_eq_of_le h1 with hlt | rfl
  · exact (twoGap_pos h0 hlt).le
  · simp

theorem twoGap_eq_zero_iff {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    twoGap r = 0 ↔ r = 1 := by
  constructor
  · intro h
    by_contra hne
    have hpos := twoGap_pos h0 (lt_of_le_of_ne h1 hne)
    linarith
  · rintro rfl
    exact twoGap_one

def twoEntropyModel (r : ℝ) : ℝ :=
  Real.log 2 - Real.log (1 + r ^ 2) / 2 + r / 2

theorem normalized_trapezoid_entropy {a b : ℝ} (ha : 0 < a)
    (hunit : a ^ 2 + b ^ 2 = 1) :
    Real.log (2 * a) + b / (2 * a) = twoEntropyModel (b / a) := by
  have hprod : a ^ 2 * (1 + (b / a) ^ 2) = 1 := by
    calc
      _ = a ^ 2 + b ^ 2 := by field_simp [ha.ne']
      _ = 1 := hunit
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul (pow_ne_zero 2 ha.ne') (by positivity), Real.log_pow] at hlog
  simp only [Real.log_one, Nat.cast_ofNat] at hlog
  have hratio : b / (2 * a) = (b / a) / 2 := by ring
  unfold twoEntropyModel
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne', hratio]
  linarith

theorem twoEntropyModel_gap (r : ℝ) :
    twoEntropyModel 1 - twoEntropyModel r = twoGap r := by
  unfold twoEntropyModel twoGap
  rw [Real.log_div (by positivity) (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring

theorem twoEntropyModel_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    twoEntropyModel r ≤ twoEntropyModel 1 := by
  have h := twoGap_nonneg h0 h1
  rw [← twoEntropyModel_gap] at h
  linarith

theorem twoEntropyModel_eq_iff {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    twoEntropyModel r = twoEntropyModel 1 ↔ r = 1 := by
  constructor
  · intro h
    apply (twoGap_eq_zero_iff h0 h1).mp
    rw [← twoEntropyModel_gap, h, sub_self]
  · rintro rfl
    rfl

end
end ENT
