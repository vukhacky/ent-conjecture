module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Finite, kernel-checked elementary-function enclosure rules.

Every bound is an implication from explicit finite arithmetic inequalities.
No numerical library output is assumed to be sound. The same rules support
rational point evaluations and uniform polynomial-in-function quadrature.
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace ENT.Small.Enclosures

noncomputable section

def expTaylor (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ range n, x ^ k / (k.factorial : ℝ)

def expError (n : ℕ) (r : ℝ) : ℝ :=
  r ^ n * ((n + 1 : ℕ) : ℝ) / ((n.factorial : ℝ) * (n : ℝ))

theorem exp_taylor_error {n : ℕ} (hn : 0 < n) {x r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hx : |x| ≤ r) :
    |Real.exp x - expTaylor n x| ≤ expError n r := by
  have h := Real.exp_bound (hx.trans hr1) hn
  apply h.trans
  unfold expError
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx n
  have hc : 0 ≤ ((n + 1 : ℕ) : ℝ) / ((n.factorial : ℝ) * (n : ℝ)) := by positivity
  have he := mul_le_mul_of_nonneg_right hp hc
  convert he using 1 <;> push_cast <;> ring

theorem exp_taylor_bounds {n : ℕ} (hn : 0 < n) {x r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hx : |x| ≤ r) :
    expTaylor n x - expError n r ≤ Real.exp x ∧
      Real.exp x ≤ expTaylor n x + expError n r := by
  have h := abs_le.mp (exp_taylor_error hn hr0 hr1 hx)
  constructor <;> linarith

theorem exp_enclosure_of_taylor {n : ℕ} (hn : 0 < n) {x r l u : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hx : |x| ≤ r)
    (hl : l ≤ expTaylor n x - expError n r)
    (hu : expTaylor n x + expError n r ≤ u) :
    l ≤ Real.exp x ∧ Real.exp x ≤ u :=
  ⟨hl.trans (exp_taylor_bounds hn hr0 hr1 hx).1,
    (exp_taylor_bounds hn hr0 hr1 hx).2.trans hu⟩

/-- Safe range reconstruction after argument division by an integer. -/
theorem exp_scale_pow_enclosure {x l u : ℝ} (hl0 : 0 ≤ l)
    (hl : l ≤ Real.exp x) (hu : Real.exp x ≤ u) (n : ℕ) :
    l ^ n ≤ Real.exp ((n : ℝ) * x) ∧ Real.exp ((n : ℝ) * x) ≤ u ^ n := by
  rw [Real.exp_natCast_mul]
  exact ⟨pow_le_pow_left₀ hl0 hl n, pow_le_pow_left₀ (Real.exp_pos x).le hu n⟩

def logTaylor (n : ℕ) (x : ℝ) : ℝ :=
  -(∑ k ∈ range n, (-x) ^ (k + 1) / ((k + 1 : ℕ) : ℝ))

def logError (n : ℕ) (r : ℝ) : ℝ := r ^ (n + 1) / (1 - r)

theorem log_taylor_error {n : ℕ} {x r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : |x| ≤ r) :
    |Real.log (1 + x) - logTaylor n x| ≤ logError n r := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |-x| < 1 by simpa only [abs_neg] using hx.trans_lt hr1) n
  have he : |Real.log (1 + x) - logTaylor n x| ≤
      |x| ^ (n + 1) / (1 - |x|) := by
    simpa only [logTaylor, sub_neg_eq_add, abs_neg, add_comm, Nat.cast_add, Nat.cast_one] using h
  apply he.trans
  unfold logError
  calc
    _ ≤ r ^ (n + 1) / (1 - |x|) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg x) hx _) (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hr0 _) (by linarith) (by linarith)

theorem log_taylor_bounds {n : ℕ} {x r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : |x| ≤ r) :
    logTaylor n x - logError n r ≤ Real.log (1 + x) ∧
      Real.log (1 + x) ≤ logTaylor n x + logError n r := by
  have h := abs_le.mp (log_taylor_error (n := n) hr0 hr1 hx)
  constructor <;> linarith

def artanhTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)

def artanhError (n : ℕ) (x : ℝ) : ℝ := x ^ (2 * n + 1) / (1 - x ^ 2)

theorem artanh_taylor_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    artanhTaylor n x ≤ Real.artanh x ∧
      Real.artanh x ≤ artanhTaylor n x + artanhError n x := by
  constructor
  · simpa only [artanhTaylor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      using Real.sum_range_le_artanh hx0 hx1 n
  · simpa only [artanhTaylor, artanhError, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      using Real.artanh_le_sum_range_add hx0 hx1 n

theorem log_ratio_taylor_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    2 * artanhTaylor n x ≤ Real.log ((1 + x) / (1 - x)) ∧
      Real.log ((1 + x) / (1 - x)) ≤ 2 * (artanhTaylor n x + artanhError n x) := by
  have hl := Real.sum_range_le_log_div hx0 hx1 n
  have hu := Real.log_div_le_sum_range_add hx0 hx1 n
  have hl' : artanhTaylor n x ≤ (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) := by
    simpa only [artanhTaylor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hl
  have hu' : (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) ≤
      artanhTaylor n x + artanhError n x := by
    simpa only [artanhTaylor, artanhError, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hu
  constructor <;> linarith

theorem sqrt_enclosure {x l u : ℝ} (hl0 : 0 ≤ l) (hu0 : 0 ≤ u)
    (hl : l ^ 2 ≤ x) (hu : x ≤ u ^ 2) : l ≤ Real.sqrt x ∧ Real.sqrt x ≤ u := by
  have hx : 0 ≤ x := (sq_nonneg l).trans hl
  have hs := Real.sq_sqrt hx
  constructor <;> nlinarith [Real.sqrt_nonneg x]

theorem reciprocal_enclosure {x l u : ℝ} (hl0 : 0 < l)
    (hl : l ≤ x) (hu : x ≤ u) : 1 / u ≤ 1 / x ∧ 1 / x ≤ 1 / l :=
  ⟨one_div_le_one_div_of_le (hl0.trans_le hl) hu,
    one_div_le_one_div_of_le hl0 hl⟩

end
end ENT.Small.Enclosures
