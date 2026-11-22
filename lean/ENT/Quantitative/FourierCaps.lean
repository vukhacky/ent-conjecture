module

public import ENT.Pang.EnvelopeBounds
public import ENT.Pang.TailBounds
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Unrounded dimension-dependent envelope moment bounds. -/

@[expose] public section
set_option autoImplicit false
open Filter
open scoped Topology
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

def momentMajorant (n : ℕ) : ℕ → ℝ
  | 0 => (2 * (n : ℝ) - 3) / (2 * ((n : ℝ) - 3))
  | k + 1 => ((2*k+1 : ℕ) : ℝ) * (n : ℝ) /
      ((n : ℝ) - 2*(k : ℝ) - 4) * momentMajorant n k

theorem momentMajorant_pos {n : ℕ} (hn : 16 ≤ n) :
    ∀ k : ℕ, k ≤ 6 → 0 < momentMajorant n k := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  intro k
  induction k with
  | zero =>
    intro _
    exact div_pos (by linarith) (by linarith)
  | succ k ih =>
    intro hk
    have hkR : (k : ℝ) ≤ 5 := by exact_mod_cast (by omega : k ≤ 5)
    change 0 < ((2*k+1 : ℕ) : ℝ) * (n : ℝ) /
      ((n : ℝ) - 2*(k : ℝ) - 4) * momentMajorant n k
    apply mul_pos _ (ih (by omega))
    exact div_pos (by positivity) (by linarith)

theorem envelopeMoment_le_majorant {n : ℕ} (hn : 16 ≤ n) :
    ∀ k : ℕ, k ≤ 6 → envelopeMoment n k ≤ momentMajorant n k := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  intro k
  induction k with
  | zero => exact fun _ => envelopeMoment_zero_le (by omega)
  | succ k ih =>
    intro hk
    have hkR : (k : ℝ) ≤ 5 := by exact_mod_cast (by omega : k ≤ 5)
    rw [envelopeMoment_succ (by omega : 2*k+5<n), momentMajorant]
    exact mul_le_mul_of_nonneg_left (ih (by omega))
      (div_nonneg (by positivity) (by linarith))

theorem shift_fraction_antitone {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x ≤ y) :
    y / (y-a) ≤ x / (x-a) := by
  apply (div_le_div_iff₀ (by linarith : 0 < y-a) (by linarith : 0 < x-a)).mpr
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hxy)]

theorem momentMajorant_antitone {m n : ℕ} (hm : 16 ≤ m) (hmn : m ≤ n) :
    ∀ k : ℕ, k ≤ 6 → momentMajorant n k ≤ momentMajorant m k := by
  have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  intro k
  induction k with
  | zero =>
    intro _
    change (2*(n:ℝ)-3)/(2*((n:ℝ)-3)) ≤ (2*(m:ℝ)-3)/(2*((m:ℝ)-3))
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  | succ k ih =>
    intro hk
    have hkR : (k : ℝ) ≤ 5 := by exact_mod_cast (by omega : k ≤ 5)
    have hfrac := shift_fraction_antitone
      (show 0 ≤ 2*(k:ℝ)+4 by positivity)
      (show 2*(k:ℝ)+4 < (m:ℝ) by linarith) hmnR
    have hfac : ((2*k+1 : ℕ):ℝ)*(n:ℝ)/((n:ℝ)-2*(k:ℝ)-4) ≤
        ((2*k+1 : ℕ):ℝ)*(m:ℝ)/((m:ℝ)-2*(k:ℝ)-4) := by
      convert mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg (2*k+1)) using 1 <;> ring
    rw [momentMajorant, momentMajorant]
    exact mul_le_mul hfac (ih (by omega))
      (momentMajorant_pos (by omega : 16 ≤ n) k (by omega)).le
      (div_nonneg (by positivity) (by linarith))

theorem envelopeMoment_le_at256 {n : ℕ} (hn : 256 ≤ n) (k : ℕ) (hk : k ≤ 6) :
    envelopeMoment n k ≤ momentMajorant 256 k :=
  (envelopeMoment_le_majorant (by omega) k hk).trans
    (momentMajorant_antitone (by omega : 16 ≤ 256) hn k hk)

theorem envelopeMoment_zero_le_at256 {n : ℕ} (hn : 256 ≤ n) :
    envelopeMoment n 0 ≤ 509/506 := by
  have h := envelopeMoment_le_at256 hn 0 (by norm_num)
  norm_num [momentMajorant] at h ⊢
  exact h

end
end ENT.Quantitative
