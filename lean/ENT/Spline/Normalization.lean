module

public import ENT.Spline.CellGluing

/-! Positive normalization changes a negative log by a local additive constant,
so its third derivative agrees with the unnormalized potential. -/

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology

namespace ENT.Spline

noncomputable section

def normalizationConstant (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) / 2 * (Nat.factorial (n - 1) : ℝ)⁻¹

theorem normalizationConstant_pos (n : ℕ) (hn : 0 < n) :
    0 < normalizationConstant n := by
  unfold normalizationConstant
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hf : 0 < (Nat.factorial (n - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos (n - 1)
  positivity

theorem diagonalSplineDensity_eq (n : ℕ) (x : ℝ) :
    diagonalSplineDensity n x = normalizationConstant n *
      unnormalizedSpline n (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2) := by
  unfold diagonalSplineDensity unitSumSplineDensity normalizationConstant
  ring

theorem third_deriv_diagonalSplinePotential_eq (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hp : unnormalizedSpline n (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2) ≠ 0) :
    deriv (deriv (deriv (diagonalSplinePotential n))) x =
      deriv (deriv (deriv (unnormalizedPotential n))) x := by
  have hc : normalizationConstant n ≠ 0 := ne_of_gt (normalizationConstant_pos n hn)
  have hcont : Continuous (fun y : ℝ =>
      unnormalizedSpline n (((n : ℝ) - Real.sqrt (n : ℝ) * y) / 2)) :=
    (continuous_unnormalizedSpline n).comp
      ((continuous_const.sub (continuous_const.mul continuous_id)).div_const 2)
  have hne := hcont.continuousAt.eventually_ne hp
  have heq : diagonalSplinePotential n =ᶠ[𝓝 x]
      (fun y => -Real.log (normalizationConstant n) + unnormalizedPotential n y) := by
    apply hne.mono
    intro y hy
    rw [diagonalSplinePotential, diagonalSplineDensity_eq, Real.log_mul hc hy]
    unfold unnormalizedPotential
    ring
  have h := (heq.iteratedDeriv 3).eq_of_nhds
  rw [iteratedDeriv_const_add (by norm_num : 0 < (3 : ℕ))] at h
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h

end
end ENT.Spline
