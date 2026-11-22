module

public import ENT.Pang.EnvelopeRecurrence

/-! Exact rational bounds for the envelope moments at the original threshold 150. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Pang

noncomputable section

def envelopeCap : ℕ → ℝ
  | 0 => 99 / 98
  | k + 1 => ((2 * k + 1 : ℕ) : ℝ) * 150 / (150 - 2 * (k : ℝ) - 4) * envelopeCap k

theorem envelopeMoment_zero_le_cap {n : ℕ} (hn : 150 ≤ n) :
    envelopeMoment n 0 ≤ envelopeCap 0 := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  apply (envelopeMoment_zero_le (by omega : 3 < n)).trans
  unfold envelopeCap
  apply (div_le_iff₀ (show 0 < 2 * ((n : ℝ) - 3) by linarith)).mpr
  linarith

theorem envelope_factor_le_at150 {n k : ℕ} (hn : 150 ≤ n) (hk : k ≤ 5) :
    ((2 * k + 1 : ℕ) : ℝ) * (n : ℝ) / ((n : ℝ) - 2 * (k : ℝ) - 4) ≤
      ((2 * k + 1 : ℕ) : ℝ) * 150 / (150 - 2 * (k : ℝ) - 4) := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (k : ℝ) ≤ 5 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hd : 0 < (n : ℝ) - 2 * (k : ℝ) - 4 := by linarith
  have hc : 0 < 150 - 2 * (k : ℝ) - 4 := by linarith
  have hf : (n : ℝ) / ((n : ℝ) - 2 * (k : ℝ) - 4) ≤
      150 / (150 - 2 * (k : ℝ) - 4) := by
    apply (div_le_div_iff₀ hd hc).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (show 0 ≤ 2 * (k : ℝ) + 4 by positivity)]
  have h := mul_le_mul_of_nonneg_left hf
    (show (0 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)
  convert h using 1 <;> ring

theorem envelopeMoment_le_cap {n : ℕ} (hn : 150 ≤ n) :
    ∀ k : ℕ, k ≤ 6 → envelopeMoment n k ≤ envelopeCap k := by
  intro k
  induction k with
  | zero => exact fun _ => envelopeMoment_zero_le_cap hn
  | succ k ih =>
    intro hk
    have hk5 : k ≤ 5 := by omega
    have hkR : (k : ℝ) ≤ 5 := by exact_mod_cast hk5
    have hfac : 0 ≤ ((2 * k + 1 : ℕ) : ℝ) * 150 / (150 - 2 * (k : ℝ) - 4) :=
      div_nonneg (by positivity) (by linarith)
    rw [envelopeMoment_succ (by omega : 2 * k + 5 < n), envelopeCap]
    exact mul_le_mul (envelope_factor_le_at150 hn hk5) (ih (by omega))
      (envelopeMoment_nonneg (by omega : 0 < n) k) hfac

theorem envelopeMoment_order2_lt {n : ℕ} (hn : 150 ≤ n) :
    envelopeMoment n 1 < 21 / 20 :=
  (envelopeMoment_le_cap hn 1 (by norm_num)).trans_lt (by norm_num [envelopeCap])

theorem envelopeMoment_order4_lt {n : ℕ} (hn : 150 ≤ n) : envelopeMoment n 2 < 5 :=
  (envelopeMoment_le_cap hn 2 (by norm_num)).trans_lt (by norm_num [envelopeCap])

theorem envelopeMoment_order6_lt {n : ℕ} (hn : 150 ≤ n) : envelopeMoment n 3 < 24 :=
  (envelopeMoment_le_cap hn 3 (by norm_num)).trans_lt (by norm_num [envelopeCap])

theorem envelopeMoment_order10_lt {n : ℕ} (hn : 150 ≤ n) : envelopeMoment n 5 < 1500 :=
  (envelopeMoment_le_cap hn 5 (by norm_num)).trans_lt (by norm_num [envelopeCap])

theorem envelopeMoment_order12_lt {n : ℕ} (hn : 150 ≤ n) : envelopeMoment n 6 < 16000 :=
  (envelopeMoment_le_cap hn 6 (by norm_num)).trans_lt (by norm_num [envelopeCap])

/-- The five estimates in Pang Appendix B, Lemma B.1. -/
theorem pang_envelope_moment_bounds {n : ℕ} (hn : 150 ≤ n) :
    envelopeMoment n 1 < 21 / 20 ∧ envelopeMoment n 2 < 5 ∧
      envelopeMoment n 3 < 24 ∧ envelopeMoment n 5 < 1500 ∧ envelopeMoment n 6 < 16000 :=
  ⟨envelopeMoment_order2_lt hn, envelopeMoment_order4_lt hn,
    envelopeMoment_order6_lt hn, envelopeMoment_order10_lt hn, envelopeMoment_order12_lt hn⟩

end
end ENT.Pang
