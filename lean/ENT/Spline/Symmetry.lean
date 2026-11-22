module

public import ENT.Spline.PositiveInterior

/-! Reflection symmetry of the genuine spline density, obtained from its
proved convolution-window recurrence. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory

namespace ENT.Spline

noncomputable section

theorem unitSumSplineDensity_reflection (n : ℕ) (hn : 2 ≤ n) :
    ∀ t : ℝ, unitSumSplineDensity n ((n : ℝ) - t) = unitSumSplineDensity n t := by
  induction n, hn using Nat.le_induction with
  | base =>
      intro t
      norm_num only [Nat.cast_ofNat]
      simp only [unitSumSplineDensity_two_overlap, min_def, max_def]
      split_ifs <;> linarith
  | succ n hn ih =>
      intro t
      rw [← unitSumSplineDensity_window n hn, ← unitSumSplineDensity_window n hn]
      calc
        (∫ y in ((n + 1 : ℕ) : ℝ) - t - 1..((n + 1 : ℕ) : ℝ) - t,
            unitSumSplineDensity n y) =
            ∫ y in (t - 1)..t, unitSumSplineDensity n ((n : ℝ) - y) := by
          rw [intervalIntegral.integral_comp_sub_left]
          congr 1 <;> push_cast <;> ring
        _ = ∫ y in (t - 1)..t, unitSumSplineDensity n y := by
          apply intervalIntegral.integral_congr
          intro y _
          exact ih y

theorem diagonalSplineDensity_even (n : ℕ) (hn : 2 ≤ n) :
    Function.Even (diagonalSplineDensity n) := by
  intro x
  unfold diagonalSplineDensity
  congr 1
  have harg : ((n : ℝ) - Real.sqrt (n : ℝ) * (-x)) / 2 =
      (n : ℝ) - (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2) := by ring
  rw [harg, unitSumSplineDensity_reflection n hn]

theorem diagonalSplinePotential_even (n : ℕ) (hn : 2 ≤ n) :
    Function.Even (diagonalSplinePotential n) := by
  intro x
  unfold diagonalSplinePotential
  rw [diagonalSplineDensity_even n hn x]

theorem deriv_zero_of_even (f : ℝ → ℝ) (hf : Function.Even f) : deriv f 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ f 0
  · have heq : (fun x : ℝ => f (-x)) = f := funext hf
    have hd' : HasDerivAt (fun x : ℝ => f (-x)) (-(deriv f 0)) 0 := by
      have hd0 : HasDerivAt f (deriv f 0) (- (0 : ℝ)) := by
        simpa only [neg_zero] using hd.hasDerivAt
      have hneg : HasDerivAt (fun x : ℝ => -x) (-1) 0 := by
        convert (hasDerivAt_id (0 : ℝ)).neg using 1
        rfl
      convert hd0.comp 0 hneg using 1 <;> first | rfl | ring
    rw [heq] at hd'
    have hu := hd'.unique hd.hasDerivAt
    linarith
  · exact deriv_zero_of_not_differentiableAt hd

theorem deriv_diagonalSplineDensity_zero (n : ℕ) (hn : 2 ≤ n) :
    deriv (diagonalSplineDensity n) 0 = 0 :=
  deriv_zero_of_even _ (diagonalSplineDensity_even n hn)

theorem deriv_diagonalSplinePotential_zero (n : ℕ) (hn : 2 ≤ n) :
    deriv (diagonalSplinePotential n) 0 = 0 :=
  deriv_zero_of_even _ (diagonalSplinePotential_even n hn)

end
end ENT.Spline
