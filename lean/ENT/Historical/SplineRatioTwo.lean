module

public import ENT.Historical.SplineRatio

/-! The triangular endpoint case of normalized slice monotonicity. -/

@[expose] public section
set_option autoImplicit false
open Set

namespace ENT.Spline
noncomputable section

theorem unitSumSplineDensity_two_first {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    unitSumSplineDensity 2 x = x := by
  rw [unitSumSplineDensity_two_overlap, min_eq_right hx1,
    max_eq_left (by linarith : x-1 ≤ 0), sub_zero, max_eq_right hx0]

theorem unitSumSplineDensity_two_second {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    unitSumSplineDensity 2 x = 2-x := by
  rw [unitSumSplineDensity_two_overlap, min_eq_left hx1,
    max_eq_right (by linarith : 0 ≤ x-1), max_eq_right (by linarith : 0 ≤ 1-(x-1))]
  ring

theorem unitSumSplineDensity_two_tail {x : ℝ} (hx2 : 2 ≤ x) :
    unitSumSplineDensity 2 x = 0 := by
  rw [unitSumSplineDensity_two_overlap, min_eq_left (by linarith : 1 ≤ x),
    max_eq_right (by linarith : 0 ≤ x-1), max_eq_left (by linarith : 1-(x-1) ≤ 0)]

theorem spline_two_ratio_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    unitSumSplineDensity 2 y / y ≤ unitSumSplineDensity 2 x / x := by
  have hy : 0 < y := hx.trans_le hxy
  by_cases hy2 : 2 ≤ y
  · rw [unitSumSplineDensity_two_tail hy2, zero_div]
    exact div_nonneg (unitSumSplineDensity_nonneg 2 (by decide) x) hx.le
  by_cases hx1 : x ≤ 1
  · rw [unitSumSplineDensity_two_first hx.le hx1, div_self hx.ne']
    apply (div_le_one hy).mpr
    by_cases hy1 : y ≤ 1
    · rw [unitSumSplineDensity_two_first hy.le hy1]
    · rw [unitSumSplineDensity_two_second (by linarith) (by linarith)]
      linarith
  · rw [unitSumSplineDensity_two_second (by linarith : 1 ≤ y) (by linarith),
      unitSumSplineDensity_two_second (by linarith : 1 ≤ x) (by linarith)]
    apply (div_le_div_iff₀ hy hx).mpr
    nlinarith

theorem normalizedSliceDensity_antitoneOn_ge_two (n : ℕ) (hn : 2 ≤ n) :
    AntitoneOn (normalizedSliceDensity n) (Ioi 0) := by
  by_cases h2 : n=2
  · subst n
    intro x hx y hy hxy
    simpa only [normalizedSliceDensity, show 2-1=1 by decide, pow_one]
      using spline_two_ratio_antitone hx hxy
  · exact normalizedSliceDensity_antitoneOn n (by omega)

theorem spline_div_power_antitone_ge_two {n : ℕ} (hn : 2 ≤ n)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    unitSumSplineDensity n y / y^(n-1) ≤ unitSumSplineDensity n x / x^(n-1) :=
  normalizedSliceDensity_antitoneOn_ge_two n hn hx (hx.trans_le hxy) hxy

end
end ENT.Spline
