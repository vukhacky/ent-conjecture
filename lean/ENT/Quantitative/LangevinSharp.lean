module

public import ENT.Quantitative.LangevinChain

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

def langevinGap (t : ℝ) : ℝ :=
  10*t^4*(Real.sinh t)^4*((Real.sinh t)^3-t^3*Real.cosh t) -
    54*(t*Real.cosh t-Real.sinh t)*((Real.sinh t)^2-t^2)^3

theorem langevinChain_eq_gap (t : ℝ) : langevinChain 0 t = 32 * langevinGap t := by
  have h3 : Real.exp (3*t) = Real.exp t ^ 3 := Real.exp_natCast_mul 3 t
  have h5 : Real.exp (5*t) = Real.exp t ^ 5 := Real.exp_natCast_mul 5 t
  have h7 : Real.exp (7*t) = Real.exp t ^ 7 := Real.exp_natCast_mul 7 t
  have h3' : Real.exp (t*3) = Real.exp t ^ 3 := Real.exp_mul_natCast t 3
  have h5' : Real.exp (t*5) = Real.exp t ^ 5 := Real.exp_mul_natCast t 5
  have h7' : Real.exp (t*7) = Real.exp t ^ 7 := Real.exp_mul_natCast t 7
  norm_num [langevinChain, hyperbolicPoly,
      langevinP7, langevinQ7, langevinP5, langevinQ5,
      langevinP3, langevinQ3, langevinP1, langevinQ1, langevinGap,
      Real.sinh_eq, Real.cosh_eq, Real.exp_neg, Real.exp_natCast_mul, Real.exp_mul_natCast, h3, h5, h7, h3', h5', h7']
  field_simp
  ring

theorem langevinGap_pos {t : ℝ} (ht : 0 < t) : 0 < langevinGap t := by
  have h := langevinChain_pos ht
  rw [langevinChain_eq_gap] at h
  linarith

theorem sharp_langevin_ratio {t : ℝ} (ht : 0 < t) :
    (54 : ℝ)/5 < -tiltThirdCumulant t / (tiltMean t * tiltVariance t^3) := by
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hm := tiltMean_pos ht
  have hv := tiltVariance_pos ht
  have hgap := langevinGap_pos ht
  have hid : 5*t^7*(Real.sinh t)^7 *
      (-tiltThirdCumulant t - ((54:ℝ)/5)*tiltMean t*tiltVariance t^3) = langevinGap t := by
    unfold tiltThirdCumulant tiltMean tiltVariance langevinGap
    field_simp [ht.ne', hs.ne']
    <;> ring
  have hp : 0 < 5*t^7*(Real.sinh t)^7 := by positivity
  have hd : 0 < -tiltThirdCumulant t - ((54:ℝ)/5)*tiltMean t*tiltVariance t^3 := by
    exact (mul_pos_iff_of_pos_left hp).mp (hid.symm ▸ hgap)
  apply (lt_div_iff₀ (mul_pos hm (pow_pos hv 3))).mpr
  nlinarith

end
end ENT.Quantitative
