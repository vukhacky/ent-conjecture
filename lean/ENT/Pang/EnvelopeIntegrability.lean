module

public import ENT.Pang.SineSum
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Absolute integrability of every admissible envelope moment

The optimal elementary threshold is `k + 2 < n`. This supplies the genuine
dominating functions needed by Fourier inversion and three differentiations.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory

namespace ENT.Pang

noncomputable section

theorem continuous_pangEnvelope {n : ℕ} (hn : 0 < n) : Continuous (pangEnvelope n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold pangEnvelope
  apply Continuous.rpow_const (by fun_prop)
  intro u
  left
  positivity

theorem integrable_scaled_envelope {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r) :
    Integrable (fun u : ℝ => (1 + u ^ 2 / (n : ℝ)) ^ (-r / 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  have hbase : Integrable (fun u : ℝ => (1 + ‖u‖ ^ 2) ^ (-r / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using hr)
  have h := hbase.comp_mul_left' (inv_ne_zero hs)
  convert h using 1
  funext u
  rw [Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, Real.sq_sqrt hnR.le]
  congr 2
  ring

theorem abs_pow_mul_envelope_le {n : ℕ} (hn : 0 < n) (k : ℕ) (u : ℝ) :
    |u| ^ k * pangEnvelope n u ≤
      Real.sqrt (n : ℝ) ^ k *
        (1 + u ^ 2 / (n : ℝ)) ^ (-((n : ℝ) - 1 - (k : ℝ)) / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < 1 + u ^ 2 / (n : ℝ) := by positivity
  have hroot : |u| ≤ Real.sqrt (n : ℝ) * Real.sqrt (1 + u ^ 2 / (n : ℝ)) := by
    have hsq : (Real.sqrt (n : ℝ) * Real.sqrt (1 + u ^ 2 / (n : ℝ))) ^ 2 =
        (n : ℝ) + u ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hnR.le, Real.sq_sqrt hb.le]
      field_simp [hnR.ne']
    have ha : |u| ^ 2 = u ^ 2 := sq_abs u
    have hr : 0 ≤ Real.sqrt (n : ℝ) * Real.sqrt (1 + u ^ 2 / (n : ℝ)) := by positivity
    nlinarith [abs_nonneg u]
  have hp := pow_le_pow_left₀ (abs_nonneg u) hroot k
  rw [mul_pow] at hp
  have he : Real.sqrt (1 + u ^ 2 / (n : ℝ)) ^ k =
      (1 + u ^ 2 / (n : ℝ)) ^ ((k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    congr 1
    ring
  rw [he] at hp
  calc
    |u| ^ k * pangEnvelope n u ≤
        (Real.sqrt (n : ℝ) ^ k * (1 + u ^ 2 / (n : ℝ)) ^ ((k : ℝ) / 2)) *
          (1 + u ^ 2 / (n : ℝ)) ^ (-((n : ℝ) - 1) / 2) :=
      mul_le_mul_of_nonneg_right hp (pangEnvelope_pos hn u).le
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hb]
      congr 2
      ring

theorem integrable_abs_pow_mul_pangEnvelope {n k : ℕ} (hn : k + 2 < n) :
    Integrable (fun u : ℝ => |u| ^ k * pangEnvelope n u) := by
  have hn0 : 0 < n := by omega
  have hnr : (k : ℝ) + 2 < n := by exact_mod_cast hn
  have hr : 1 < (n : ℝ) - 1 - (k : ℝ) := by linarith
  apply ((integrable_scaled_envelope hn0 hr).const_mul (Real.sqrt (n : ℝ) ^ k)).mono'
  · exact ((continuous_abs.pow k).mul (continuous_pangEnvelope hn0)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _)
        (pangEnvelope_pos hn0 u).le)]
      exact abs_pow_mul_envelope_le hn0 k u)

theorem integrable_abs_pow_mul_pangEnvelope_large {n k : ℕ}
    (hn : 150 ≤ n) (hk : k ≤ 3) :
    Integrable (fun u : ℝ => |u| ^ k * pangEnvelope n u) :=
  integrable_abs_pow_mul_pangEnvelope (by omega)

end
end ENT.Pang
