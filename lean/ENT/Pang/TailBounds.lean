module

public import ENT.Pang.GaussianMoments

/-! Actual tail integrals and the three estimates of Pang Lemma B.2(i). -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

def pangTail (n : ℕ) : Set ℝ := {u | Real.sqrt (n : ℝ) / 2 < |u|}

def normalizedTailMoment (n k : ℕ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) *
    ∫ u in pangTail n, u ^ (2 * k) * (gaussianWeight u + pangEnvelope n u)

theorem measurableSet_pangTail (n : ℕ) : MeasurableSet (pangTail n) :=
  measurableSet_lt measurable_const (continuous_abs.measurable)

theorem combinedWeight_nonneg {n : ℕ} (hn : 0 < n) (u : ℝ) :
    0 ≤ gaussianWeight u + pangEnvelope n u :=
  add_nonneg (gaussianWeight_pos u).le (pangEnvelope_pos hn u).le

theorem integrable_pow_mul_combinedWeight {n k : ℕ} (hn : k + 2 < n) :
    Integrable (fun u : ℝ => u ^ k * (gaussianWeight u + pangEnvelope n u)) := by
  have h := (integrable_pow_mul_gaussianWeight k).add (integrable_pow_mul_pangEnvelope hn)
  apply h.congr
  exact Filter.Eventually.of_forall (fun u => by dsimp; ring)

theorem normalized_integral_combinedWeight {n k : ℕ} (hn : 2 * k + 2 < n) :
    (1 / Real.sqrt (2 * Real.pi)) *
      (∫ u : ℝ, u ^ (2 * k) * (gaussianWeight u + pangEnvelope n u)) =
        gaussianMoment k + envelopeMoment n k := by
  simp_rw [mul_add]
  rw [integral_add (integrable_pow_mul_gaussianWeight _) (integrable_pow_mul_pangEnvelope hn)]
  unfold gaussianMoment envelopeMoment
  ring

theorem tail_even_power_le {n k q : ℕ} (hn : 0 < n) (hkq : k ≤ q) {u : ℝ}
    (hu : u ∈ pangTail n) :
    u ^ (2 * k) ≤ (4 / (n : ℝ)) ^ (q - k) * u ^ (2 * q) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := pow_le_pow_left₀ (show 0 ≤ Real.sqrt (n : ℝ) / 2 by positivity) hu.le 2
  rw [div_pow, Real.sq_sqrt hnR.le, sq_abs] at hsq
  have hb : 1 ≤ (4 / (n : ℝ)) * u ^ 2 := by
    rw [show (4 / (n : ℝ)) * u ^ 2 = 4 * u ^ 2 / (n : ℝ) by ring]
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hb (q - k)
  rw [one_pow] at hp
  have hu0 : 0 ≤ u ^ (2 * k) := by rw [pow_mul]; positivity
  calc
    u ^ (2 * k) = u ^ (2 * k) * 1 := by ring
    _ ≤ u ^ (2 * k) * ((4 / (n : ℝ)) * u ^ 2) ^ (q - k) :=
      mul_le_mul_of_nonneg_left hp hu0
    _ = (4 / (n : ℝ)) ^ (q - k) * u ^ (2 * q) := by
      rw [mul_pow, ← pow_mul]
      calc
        _ = (4 / (n : ℝ)) ^ (q - k) * (u ^ (2 * k) * u ^ (2 * (q - k))) := by ring
        _ = _ := by rw [← pow_add]; congr 2; omega

theorem normalizedTailMoment_le {n k q : ℕ} (hn : 2 * q + 2 < n) (hkq : k ≤ q) :
    normalizedTailMoment n k ≤
      (4 / (n : ℝ)) ^ (q - k) * (gaussianMoment q + envelopeMoment n q) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hk : 2 * k + 2 < n := by omega
  have hf := integrable_pow_mul_combinedWeight hk
  have hq := integrable_pow_mul_combinedWeight hn
  have hg : Integrable (fun u : ℝ => (4 / (n : ℝ)) ^ (q - k) *
      (u ^ (2 * q) * (gaussianWeight u + pangEnvelope n u))) := hq.const_mul _
  have hcomp : (∫ u in pangTail n, u ^ (2 * k) * (gaussianWeight u + pangEnvelope n u)) ≤
      ∫ u, (4 / (n : ℝ)) ^ (q - k) * (u ^ (2 * q) *
        (gaussianWeight u + pangEnvelope n u)) := by
    apply (setIntegral_mono_on hf.integrableOn hg.integrableOn (measurableSet_pangTail n) ?_).trans
    · apply setIntegral_le_integral hg
      exact Filter.Eventually.of_forall (fun u => by
        have hu : 0 ≤ u ^ (2 * q) := by rw [pow_mul]; positivity
        exact mul_nonneg (by positivity) (mul_nonneg hu (combinedWeight_nonneg hn0 u)))
    · intro u hu
      have h := mul_le_mul_of_nonneg_right (tail_even_power_le hn0 hkq hu)
        (combinedWeight_nonneg hn0 u)
      convert h using 1 <;> ring
  rw [integral_const_mul] at hcomp
  have h := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ 1 / Real.sqrt (2 * Real.pi) by positivity)
  unfold normalizedTailMoment
  calc
    _ ≤ (4 / (n : ℝ)) ^ (q - k) * ((1 / Real.sqrt (2 * Real.pi)) *
        ∫ u : ℝ, u ^ (2 * q) * (gaussianWeight u + pangEnvelope n u)) := by
      convert h using 1 <;> ring
    _ = _ := by rw [normalized_integral_combinedWeight hn]

theorem normalizedTailMoment_zero_lt {n : ℕ} (hn : 150 ≤ n) :
    normalizedTailMoment n 0 < 1 / (n : ℝ) := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := normalizedTailMoment_le (n := n) (k := 0) (q := 3) (by omega) (by omega)
  rw [gaussianMoment_three] at h
  have hm := envelopeMoment_order6_lt hn
  have hstrict : (4 / (n : ℝ)) ^ 3 * (15 + envelopeMoment n 3) <
      (4 / (n : ℝ)) ^ 3 * 39 :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  apply (h.trans_lt hstrict).trans
  have he : (4 / (n : ℝ)) ^ 3 * 39 = 2496 / (n : ℝ) ^ 3 := by ring
  rw [he]
  apply (div_lt_div_iff₀ (pow_pos hn0 _) hn0).mpr
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 150) hnR 2
  have hbase : (2496 : ℝ) < (n : ℝ) ^ 2 := by norm_num at hp; linarith
  nlinarith [mul_lt_mul_of_pos_right hbase hn0]

theorem normalizedTailMoment_order4_lt {n : ℕ} (hn : 150 ≤ n) :
    normalizedTailMoment n 2 < 3 / (n : ℝ) := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := normalizedTailMoment_le (n := n) (k := 2) (q := 6) (by omega) (by omega)
  rw [gaussianMoment_six] at h
  have hm := envelopeMoment_order12_lt hn
  have hstrict : (4 / (n : ℝ)) ^ 4 * (10395 + envelopeMoment n 6) <
      (4 / (n : ℝ)) ^ 4 * 26395 :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  apply (h.trans_lt hstrict).trans
  have he : (4 / (n : ℝ)) ^ 4 * 26395 = 6757120 / (n : ℝ) ^ 4 := by ring
  rw [he]
  apply (div_lt_div_iff₀ (pow_pos hn0 _) hn0).mpr
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 150) hnR 3
  have hbase : (6757120 : ℝ) < 3 * (n : ℝ) ^ 3 := by norm_num at hp; linarith
  nlinarith [mul_lt_mul_of_pos_right hbase hn0]

theorem normalizedTailMoment_order6_lt {n : ℕ} (hn : 150 ≤ n) :
    normalizedTailMoment n 3 < 3 / 5 := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := normalizedTailMoment_le (n := n) (k := 3) (q := 6) (by omega) (by omega)
  rw [gaussianMoment_six] at h
  have hm := envelopeMoment_order12_lt hn
  have hstrict : (4 / (n : ℝ)) ^ 3 * (10395 + envelopeMoment n 6) <
      (4 / (n : ℝ)) ^ 3 * 26395 :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  apply (h.trans_lt hstrict).trans
  have he : (4 / (n : ℝ)) ^ 3 * 26395 = 1689280 / (n : ℝ) ^ 3 := by ring
  rw [he]
  apply (div_lt_iff₀ (pow_pos hn0 _)).mpr
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 150) hnR 3
  norm_num at hp
  linarith

/-- The three tail estimates (69)–(71), preserving the original threshold. -/
theorem pang_tail_moment_bounds {n : ℕ} (hn : 150 ≤ n) :
    normalizedTailMoment n 0 < 1 / (n : ℝ) ∧
      normalizedTailMoment n 2 < 3 / (n : ℝ) ∧
      normalizedTailMoment n 3 < 3 / 5 :=
  ⟨normalizedTailMoment_zero_lt hn, normalizedTailMoment_order4_lt hn,
    normalizedTailMoment_order6_lt hn⟩

end
end ENT.Pang
