module

public import ENT.Pang.SineConvex
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Exact finite-interval logarithm bound for the local characteristic radius. -/

@[expose] public section

set_option autoImplicit false

open Set

namespace ENT.Pang

noncomputable section

def localLogGap (s : ℝ) : ℝ := Real.log (1 - s / 2) + s / 2 + s ^ 2 / 7

theorem hasDerivAt_localLogGap {s : ℝ} (hs : s < 2) :
    HasDerivAt localLogGap (s * (1 - 4 * s) / (14 * (2 - s))) s := by
  have hn : 1 - s / 2 ≠ 0 := by linarith
  have hn' : 2 - s ≠ 0 := by linarith
  have h := ((((hasDerivAt_const s (1 : ℝ)).sub
    ((hasDerivAt_id s).div_const 2)).log hn).add
    ((hasDerivAt_id s).div_const 2)).add (((hasDerivAt_id s).pow 2).div_const 7)
  apply h.congr_deriv
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one, id_eq, Pi.sub_apply]
  field_simp [hn, hn']
  ring

theorem localLogGap_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 4) :
    0 ≤ localLogGap s := by
  have hm : MonotoneOn localLogGap (Icc (0 : ℝ) (1 / 4)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx
      exact (hasDerivAt_localLogGap (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact (hasDerivAt_localLogGap (by linarith [hx'.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hasDerivAt_localLogGap (by linarith [hx'.2])).deriv]
      exact div_nonneg (mul_nonneg hx'.1 (by linarith [hx'.2]))
        (mul_nonneg (by norm_num) (by linarith [hx'.2]))
  have h := hm (show (0 : ℝ) ∈ Icc 0 (1 / 4) by norm_num) ⟨hs0, hs1⟩ hs0
  simpa [localLogGap] using h

theorem log_one_sub_half_lower {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 4) :
    -s / 2 - s ^ 2 / 7 ≤ Real.log (1 - s / 2) := by
  have h := localLogGap_nonneg hs0 hs1
  unfold localLogGap at h
  linarith

theorem gaussian_lower_power {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    Real.exp (-u ^ 2 / 2 - u ^ 4 / (7 * (n : ℝ))) ≤
      (1 - u ^ 2 / (2 * (n : ℝ))) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ u ^ 2 / (n : ℝ) := by positivity
  have hlog := mul_le_mul_of_nonneg_left (log_one_sub_half_lower hs0 hu) hnR.le
  have hleft : (n : ℝ) * (-(u ^ 2 / (n : ℝ)) / 2 - (u ^ 2 / (n : ℝ)) ^ 2 / 7) =
      -u ^ 2 / 2 - u ^ 4 / (7 * (n : ℝ)) := by
    field_simp [hnR.ne']
  have hbase : 1 - u ^ 2 / (n : ℝ) / 2 = 1 - u ^ 2 / (2 * (n : ℝ)) := by ring
  rw [hleft, hbase] at hlog
  have hb : 0 < 1 - u ^ 2 / (2 * (n : ℝ)) := by
    have he : u ^ 2 / (2 * (n : ℝ)) = (u ^ 2 / (n : ℝ)) / 2 := by ring
    rw [he]
    linarith
  have h := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_natCast_mul, Real.exp_log hb] at h

end
end ENT.Pang
