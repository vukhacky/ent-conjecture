module

public import ENT.Quantitative.LangevinStrongChain
public import ENT.Quantitative.FourierSkew

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

def strongLangevinGap (t : ℝ) : ℝ :=
  10*t^4*(Real.sinh t)^4*((Real.sinh t)^3-t^3*Real.cosh t) -
    54*(t*Real.cosh t-Real.sinh t)*((Real.sinh t)^2-t^2)^3 -
    60*(t*Real.cosh t-Real.sinh t)*(t^3*Real.cosh t-(Real.sinh t)^3)^2

theorem strongLangevinChain_eq_gap (t : ℝ) : strongLangevinChain 0 t = 32 * strongLangevinGap t := by
  have h3 : Real.exp (3*t) = Real.exp t ^ 3 := Real.exp_natCast_mul 3 t
  have h5 : Real.exp (5*t) = Real.exp t ^ 5 := Real.exp_natCast_mul 5 t
  have h7 : Real.exp (7*t) = Real.exp t ^ 7 := Real.exp_natCast_mul 7 t
  have h3' : Real.exp (t*3) = Real.exp t ^ 3 := Real.exp_mul_natCast t 3
  have h5' : Real.exp (t*5) = Real.exp t ^ 5 := Real.exp_mul_natCast t 5
  have h7' : Real.exp (t*7) = Real.exp t ^ 7 := Real.exp_mul_natCast t 7
  norm_num [strongLangevinChain, hyperbolicPoly,
      strongLangevinP7, strongLangevinQ7, strongLangevinP5, strongLangevinQ5,
      strongLangevinP3, strongLangevinQ3, strongLangevinP1, strongLangevinQ1, strongLangevinGap,
      Real.sinh_eq, Real.cosh_eq, Real.exp_neg, Real.exp_natCast_mul, Real.exp_mul_natCast, h3, h5, h7, h3', h5', h7']
  field_simp
  ring

theorem strongLangevinGap_pos {t : ℝ} (ht : 0 < t) : 0 < strongLangevinGap t := by
  have h := strongLangevinChain_pos ht
  rw [strongLangevinChain_eq_gap] at h
  linarith

theorem strong_langevin_ratio {t : ℝ} (ht : 0 < t) :
    (54 : ℝ)/5 + 3*skewSquared t < -tiltThirdCumulant t / (tiltMean t * tiltVariance t^3) := by
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hm := tiltMean_pos ht
  have hv := tiltVariance_pos ht
  have hgap := strongLangevinGap_pos ht
  have hid : 5*t^7*(Real.sinh t)^7 *
      (-tiltThirdCumulant t - ((54:ℝ)/5)*tiltMean t*tiltVariance t^3 - 3*tiltMean t*(tiltThirdCumulant t)^2) = strongLangevinGap t := by
    unfold tiltThirdCumulant tiltMean tiltVariance strongLangevinGap
    field_simp [ht.ne', hs.ne']
    <;> ring
  have hp : 0 < 5*t^7*(Real.sinh t)^7 := by positivity
  have hd : 0 < -tiltThirdCumulant t - ((54:ℝ)/5)*tiltMean t*tiltVariance t^3 - 3*tiltMean t*(tiltThirdCumulant t)^2 := by
    exact (mul_pos_iff_of_pos_left hp).mp (hid.symm ▸ hgap)
  have hq : skewSquared t * tiltVariance t^3 = (tiltThirdCumulant t)^2 := by
    unfold skewSquared
    rw [sq_abs, tiltStandardMoment_three ht, tiltSkewness, div_pow]
    have hpow : (Real.sqrt (tiltVariance t)^3)^2=tiltVariance t^3 := by
      rw [←pow_mul, mul_comm 3 2, pow_mul, Real.sq_sqrt hv.le]
    rw [hpow]
    field_simp
  apply (lt_div_iff₀ (mul_pos hm (pow_pos hv 3))).mpr
  nlinarith [congrArg (fun z : ℝ=>3*tiltMean t*z) hq]

end
end ENT.Quantitative
