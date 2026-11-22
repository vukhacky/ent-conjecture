module

public import ENT.Historical.SplineEuler

/-! Monotonicity of the capped-to-uncapped spline slice-volume ratio.
The derivative is evaluated only at positive denominators. -/

@[expose] public section
set_option autoImplicit false
open Set

namespace ENT.Spline
noncomputable section

def normalizedSliceDensity (n : ℕ) (x : ℝ) : ℝ :=
  unitSumSplineDensity n x / x^(n-1)

theorem normalizedSliceDensity_hasDerivAt (n : ℕ) (hn : 3 ≤ n)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (normalizedSliceDensity n)
      ((deriv (unitSumSplineDensity n) x * x^(n-1) -
        unitSumSplineDensity n x * ((n:ℝ)-1) * x^(n-2)) / (x^(n-1))^2) x := by
  have hd := ((contDiff_unitSumSplineDensity 1 n (by omega)).differentiable (by norm_num) x).hasDerivAt
  have h := hd.div (hasDerivAt_pow (n-1) x) (pow_ne_zero _ hx.ne')
  convert h using 1
  · rfl
  · rw [show n-1-1=n-2 by omega, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring

theorem normalizedSliceDensity_deriv_nonpos (n : ℕ) (hn : 3 ≤ n)
    (x : ℝ) (hx : 0 < x) : deriv (normalizedSliceDensity n) x ≤ 0 := by
  rw [(normalizedSliceDensity_hasDerivAt n hn x hx).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hnonneg : 0 ≤ ((n:ℝ)-1)*unitSumSplineDensity n x -
      x*deriv (unitSumSplineDensity n) x := by
    rw [unitSumSplineDensity_euler n hn x]
    exact mul_nonneg (Nat.cast_nonneg _) (unitSumSplineDensity_nonneg (n-1) (by omega) _)
  have hpow : 0 ≤ x^(n-2) := pow_nonneg hx.le _
  have he : deriv (unitSumSplineDensity n) x * x^(n-1) -
      unitSumSplineDensity n x * ((n:ℝ)-1) * x^(n-2) =
      -x^(n-2) * (((n:ℝ)-1)*unitSumSplineDensity n x -
        x*deriv (unitSumSplineDensity n) x) := by
    rw [show n-1=(n-2)+1 by omega, pow_succ]
    ring
  rw [he]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpow) hnonneg

theorem normalizedSliceDensity_antitoneOn (n : ℕ) (hn : 3 ≤ n) :
    AntitoneOn (normalizedSliceDensity n) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun x hx => (normalizedSliceDensity_hasDerivAt n hn x hx).continuousAt.continuousWithinAt)
    (fun x hx => (normalizedSliceDensity_hasDerivAt n hn x (interior_subset hx)).differentiableAt.differentiableWithinAt)
  intro x hx
  exact normalizedSliceDensity_deriv_nonpos n hn x (interior_subset hx)

theorem spline_div_power_antitone {n : ℕ} (hn : 3 ≤ n)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    unitSumSplineDensity n y / y^(n-1) ≤ unitSumSplineDensity n x / x^(n-1) :=
  normalizedSliceDensity_antitoneOn n hn hx (hx.trans_le hxy) hxy

end
end ENT.Spline
