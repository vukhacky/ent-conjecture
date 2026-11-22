module

public import ENT.Pang.EnvelopeIntegrability
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The elementary radial primitive used in the envelope mass bound. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace ENT.Pang

noncomputable section

theorem integrable_pow_mul_pangEnvelope {n k : ℕ} (hn : k + 2 < n) :
    Integrable (fun u : ℝ => u ^ k * pangEnvelope n u) := by
  have hn0 : 0 < n := by omega
  apply (integrable_abs_pow_mul_pangEnvelope hn).mono'
  · exact ((continuous_id.pow k).mul (continuous_pangEnvelope hn0)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (pangEnvelope_pos hn0 u)])

theorem tendsto_envelope_base {n : ℕ} (hn : 0 < n) :
    Tendsto (fun u : ℝ => 1 + u ^ 2 / (n : ℝ)) atTop atTop := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact tendsto_const_nhds.add_atTop
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const hnR)

def envelopeRadialPrimitive (n : ℕ) (u : ℝ) : ℝ :=
  -(n : ℝ) / ((n : ℝ) - 3) * (1 + u ^ 2 / (n : ℝ)) ^ (-((n : ℝ) - 3) / 2)

theorem hasDerivAt_envelopeRadialPrimitive {n : ℕ} (hn : 3 < n) (u : ℝ) :
    HasDerivAt (envelopeRadialPrimitive n) (u * pangEnvelope n u) u := by
  have hnR : (3 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn3 : (n : ℝ) - 3 ≠ 0 := by linarith
  have hb : 0 < 1 + u ^ 2 / (n : ℝ) := by positivity
  have h := (((hasDerivAt_const u (1 : ℝ)).add
    (((hasDerivAt_id u).pow 2).div_const (n : ℝ))).rpow_const
      (p := -((n : ℝ) - 3) / 2) (Or.inl hb.ne')).const_mul (-(n : ℝ) / ((n : ℝ) - 3))
  apply h.congr_deriv
  simp only [Pi.add_apply, Pi.pow_apply, id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, zero_add]
  have he : -((n : ℝ) - 3) / 2 - 1 = -((n : ℝ) - 1) / 2 := by ring
  rw [he]
  unfold pangEnvelope
  field_simp [hn0, hn3]

theorem tendsto_envelopeRadialPrimitive {n : ℕ} (hn : 3 < n) :
    Tendsto (envelopeRadialPrimitive n) atTop (𝓝 0) := by
  have hnR : (3 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < ((n : ℝ) - 3) / 2 := by linarith
  have h := (tendsto_rpow_neg_atTop hr).comp (tendsto_envelope_base (by omega : 0 < n))
  have he : -(((n : ℝ) - 3) / 2) = -((n : ℝ) - 3) / 2 := by ring
  simp only [he] at h
  change Tendsto (fun u : ℝ => (1 + u ^ 2 / (n : ℝ)) ^ (-((n : ℝ) - 3) / 2))
    atTop (𝓝 0) at h
  unfold envelopeRadialPrimitive
  simpa only [mul_zero] using
    h.const_mul (-(n : ℝ) / ((n : ℝ) - 3))

theorem integral_radial_envelope {n : ℕ} (hn : 3 < n) :
    (∫ u in Ioi (0 : ℝ), u * pangEnvelope n u) = (n : ℝ) / ((n : ℝ) - 3) := by
  have hi : Integrable (fun u : ℝ => u * pangEnvelope n u) := by
    simpa only [pow_one] using integrable_pow_mul_pangEnvelope (n := n) (k := 1) hn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u (_ : u ∈ Ici (0 : ℝ)) => hasDerivAt_envelopeRadialPrimitive hn u)
    hi.integrableOn (tendsto_envelopeRadialPrimitive hn)
  simpa [envelopeRadialPrimitive, neg_div] using h

end
end ENT.Pang
