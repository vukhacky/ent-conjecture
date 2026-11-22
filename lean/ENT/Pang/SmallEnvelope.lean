module

public import ENT.Pang.LocalBounds

/-! The Gaussian comparison on the small interval in Pang Lemma B.2(ii). -/

@[expose] public section

set_option autoImplicit false

open Set

namespace ENT.Pang

noncomputable section

def smallLogGap (x : ℝ) : ℝ := Real.log (1 + x) - x + x ^ 2 / 2

theorem hasDerivAt_smallLogGap {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt smallLogGap (x ^ 2 / (1 + x)) x := by
  have hn : 1 + x ≠ 0 := by positivity
  have h := ((((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hn).sub
    (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).div_const 2)
  apply h.congr_deriv
  simp only [Pi.add_apply, id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  field_simp [hn]
  ring

theorem log_one_add_lower_quadratic {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  have hm : MonotoneOn smallLogGap (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun y hy => (hasDerivAt_smallLogGap hy).continuousAt.continuousWithinAt
    · exact fun y hy => (hasDerivAt_smallLogGap (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := interior_subset hy
      rw [(hasDerivAt_smallLogGap hy0).deriv]
      exact div_nonneg (sq_nonneg _) (by positivity)
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  norm_num [smallLogGap] at h
  linarith

theorem pangEnvelope_log_exponent_le {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    Real.log (1 + u ^ 2 / (n : ℝ)) * (-((n : ℝ) - 1) / 2) + u ^ 2 / 2 ≤
      u ^ 2 / (2 * (n : ℝ)) + u ^ 4 / (4 * (n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hx : 0 ≤ u ^ 2 / (n : ℝ) := by positivity
  have hm := mul_le_mul_of_nonpos_right (log_one_add_lower_quadratic hx)
    (show -((n : ℝ) - 1) / 2 ≤ 0 by linarith)
  have he : u ^ 2 / (2 * (n : ℝ)) + u ^ 4 / (4 * (n : ℝ)) -
      ((u ^ 2 / (n : ℝ) - (u ^ 2 / (n : ℝ)) ^ 2 / 2) *
        (-((n : ℝ) - 1) / 2) + u ^ 2 / 2) = u ^ 4 / (4 * (n : ℝ) ^ 2) := by
    field_simp [hn0]
    ring
  have hp : 0 ≤ u ^ 4 / (4 * (n : ℝ) ^ 2) := by positivity
  nlinarith

theorem pangEnvelope_small_exponent_le {n : ℕ} (hn : 150 ≤ n) {u : ℝ}
    (hu : u ^ 2 ≤ 7 / 2) :
    Real.log (1 + u ^ 2 / (n : ℝ)) * (-((n : ℝ) - 1) / 2) + u ^ 2 / 2 ≤ 1 / 30 := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  apply (pangEnvelope_log_exponent_le (by omega : 1 ≤ n) u).trans
  have he : u ^ 2 / (2 * (n : ℝ)) + u ^ 4 / (4 * (n : ℝ)) =
      (2 * u ^ 2 + u ^ 4) / (4 * (n : ℝ)) := by ring
  rw [he]
  apply (div_le_iff₀ (show 0 < 4 * (n : ℝ) by linarith)).mpr
  have hp := pow_le_pow_left₀ (sq_nonneg u) hu 2
  nlinarith

/-- A strict version of the envelope comparison (72). -/
theorem pangEnvelope_small_lt_gaussian {n : ℕ} (hn : 150 ≤ n) {u : ℝ}
    (hu : u ^ 2 ≤ 7 / 2) :
    pangEnvelope n u < (21 : ℝ) / 20 * Real.exp (-u ^ 2 / 2) := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 < 1 + u ^ 2 / (n : ℝ) := by positivity
  have he := Real.exp_le_exp.mpr (pangEnvelope_small_exponent_le hn hu)
  have hex : Real.exp ((1 : ℝ) / 30) < (21 : ℝ) / 20 := by
    have h := Real.exp_bound_div_one_sub_of_interval' (by norm_num : (0 : ℝ) < 1 / 30)
      (by norm_num : (1 : ℝ) / 30 < 1)
    norm_num at h
    linarith
  have hx := he.trans_lt hex
  unfold pangEnvelope
  rw [Real.rpow_def_of_pos hb]
  calc
    Real.exp (Real.log (1 + u ^ 2 / (n : ℝ)) * (-((n : ℝ) - 1) / 2)) =
        Real.exp (Real.log (1 + u ^ 2 / (n : ℝ)) * (-((n : ℝ) - 1) / 2) + u ^ 2 / 2) *
          Real.exp (-u ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ < _ := mul_lt_mul_of_pos_right hx (Real.exp_pos _)

end
end ENT.Pang
