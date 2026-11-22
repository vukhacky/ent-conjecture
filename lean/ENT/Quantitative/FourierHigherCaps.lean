module

public import ENT.Quantitative.FourierCaps

/-! General even envelope-moment bounds, used only at an explicit finite order. -/

@[expose] public section
set_option autoImplicit false
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

theorem envelopeMoment_le_majorant_all {n : ℕ} (k : ℕ) (hn : 2*k+4≤n) :
    envelopeMoment n k ≤ momentMajorant n k := by
  induction k generalizing n with
  | zero => exact envelopeMoment_zero_le (by omega)
  | succ k ih =>
    have hnR : (2:ℝ)*k+6≤n := by exact_mod_cast (by omega : 2*k+6≤n)
    rw [envelopeMoment_succ (by omega : 2*k+5<n), momentMajorant]
    exact mul_le_mul_of_nonneg_left (ih (by omega)) (div_nonneg (by positivity) (by linarith))

theorem momentMajorant_pos_all {n : ℕ} (k : ℕ) (hn : 2*k+4≤n) :
    0<momentMajorant n k := by
  induction k generalizing n with
  | zero =>
    have hnR : (4:ℝ)≤n := by exact_mod_cast hn
    exact div_pos (by linarith) (by linarith)
  | succ k ih =>
    have hnR : (2:ℝ)*k+6≤n := by exact_mod_cast (by omega : 2*k+6≤n)
    have hn0 : (0:ℝ)<n := by linarith [Nat.cast_nonneg (α:=ℝ) k]
    rw [momentMajorant]
    exact mul_pos (div_pos (by positivity) (by linarith)) (ih (by omega))

theorem momentMajorant_antitone_all {m n : ℕ} (k : ℕ) (hm : 2*k+4≤m) (hmn : m≤n) :
    momentMajorant n k≤momentMajorant m k := by
  induction k generalizing m n with
  | zero =>
    have hmR : (4:ℝ)≤m := by exact_mod_cast hm
    have hmnR : (m:ℝ)≤n := by exact_mod_cast hmn
    change (2*(n:ℝ)-3)/(2*((n:ℝ)-3))≤(2*(m:ℝ)-3)/(2*((m:ℝ)-3))
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  | succ k ih =>
    have hmR : (2:ℝ)*k+6≤m := by exact_mod_cast (by omega : 2*k+6≤m)
    have hmnR : (m:ℝ)≤n := by exact_mod_cast hmn
    have hfrac := shift_fraction_antitone (show 0≤2*(k:ℝ)+4 by positivity)
      (show 2*(k:ℝ)+4<(m:ℝ) by linarith) hmnR
    have hfac : ((2*k+1:ℕ):ℝ)*(n:ℝ)/((n:ℝ)-2*(k:ℝ)-4)≤
        ((2*k+1:ℕ):ℝ)*(m:ℝ)/((m:ℝ)-2*(k:ℝ)-4) := by
      convert mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg (2*k+1)) using 1 <;> ring
    rw [momentMajorant,momentMajorant]
    exact mul_le_mul hfac (ih (by omega) hmn)
      (momentMajorant_pos_all k (by omega)).le (div_nonneg (by positivity) (by linarith))

theorem envelopeMoment_le_at150 {n : ℕ} (hn : 150≤n) (k : ℕ) (hk : k≤10) :
    envelopeMoment n k≤momentMajorant 150 k :=
  (envelopeMoment_le_majorant_all k (by omega)).trans
    (momentMajorant_antitone_all k (by omega) hn)

theorem threshold150_tail_order6_le {n : ℕ} (hn : 150≤n) :
    normalizedTailMoment n 3/6 ≤ 1/250 := by
  have hnR : (150:ℝ)≤n := by exact_mod_cast hn
  have hm := envelopeMoment_le_at150 hn 10 (by norm_num)
  have h := normalizedTailMoment_le (n:=n) (k:=3) (q:=10) (by omega) (by omega)
  rw [gaussianMoment_eq_cap] at h
  have hf : (4:ℝ)/(n:ℝ)≤4/150 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hb := mul_le_mul (pow_le_pow_left₀ (by positivity) hf 7)
    (add_le_add_left hm (gaussianCap 10))
    (by norm_num [gaussianCap]; linarith [envelopeMoment_nonneg (by omega : 0<n) 10])
    (by norm_num)
  norm_num only [Nat.reduceSub] at h
  have hc : (4/150:ℝ)^7*(gaussianCap 10+momentMajorant 150 10)/6≤1/250 := by
    norm_num [gaussianCap,momentMajorant]
  linarith

end
end ENT.Quantitative
