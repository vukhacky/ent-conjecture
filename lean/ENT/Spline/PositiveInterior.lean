module

public import ENT.Spline.DiagonalProperties

/-! Strict positivity on the interior of the spline support. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Spline

noncomputable section

theorem unitSumSplineDensity_pos (n : ℕ) (hn : 2 ≤ n) :
    ∀ t : ℝ, 0 < t → t < (n : ℝ) → 0 < unitSumSplineDensity n t := by
  induction n, hn using Nat.le_induction with
  | base =>
      intro t ht0 ht2
      norm_num at ht2
      rw [unitSumSplineDensity_two_overlap]
      have hlen : max 0 (t - 1) < min 1 t := by
        apply max_lt
        · exact lt_min (by norm_num) ht0
        · exact lt_min (by linarith) (by linarith)
      exact lt_of_lt_of_le (sub_pos.mpr hlen) (le_max_right _ _)
  | succ n hn ih =>
      intro t ht0 htn
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have htn' : t < (n : ℝ) + 1 := by simpa using htn
      let a : ℝ := max 0 (t - 1)
      let b : ℝ := min (n : ℝ) t
      have hab : a < b := by
        dsimp [a, b]
        apply max_lt
        · exact lt_min hn0 ht0
        · exact lt_min (by linarith) (by linarith)
      let y : ℝ := (a + b) / 2
      have hay : a < y := by dsimp [y]; linarith
      have hyb : y < b := by dsimp [y]; linarith
      have hy0 : 0 < y := lt_of_le_of_lt (le_max_left _ _) hay
      have hyn : y < (n : ℝ) := lt_of_lt_of_le hyb (min_le_left _ _)
      have hymem : y ∈ Icc (t - 1) t :=
        ⟨le_trans (le_max_right _ _) hay.le, le_trans hyb.le (min_le_right _ _)⟩
      rw [← unitSumSplineDensity_window n hn t]
      exact intervalIntegral.integral_pos (by linarith)
        (continuous_unitSumSplineDensity n).continuousOn
        (fun z _ => unitSumSplineDensity_nonneg n hn z) ⟨y, hymem, ih y hy0 hyn⟩

theorem diagonalSplineDensity_pos (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    0 < diagonalSplineDensity n x := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hr2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hlo := mul_lt_mul_of_pos_left hx.1 hr
  have hhi := mul_lt_mul_of_pos_left hx.2 hr
  unfold diagonalSplineDensity
  apply mul_pos (div_pos hr (by norm_num))
  apply unitSumSplineDensity_pos n hn
  · nlinarith [hhi, hr2]
  · nlinarith [hlo, hr2]

theorem diagonalSplinePotential_contDiffOn (r n : ℕ) (hrn : r < n - 1) :
    ContDiffOn ℝ r (diagonalSplinePotential n)
      (Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) := by
  intro x hx
  exact (contDiffAt_diagonalSplinePotential r n hrn x
    (ne_of_gt (diagonalSplineDensity_pos n (by omega) x hx))).contDiffWithinAt

end
end ENT.Spline
