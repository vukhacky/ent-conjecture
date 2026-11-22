module

public import ENT.Quantitative.EdgeworthFourierBounds
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Global Taylor estimates for the exponential on the negative half-line.
These allow Fourier expansions without a frequency-dependent smallness
assumption on the logarithmic correction. -/

@[expose] public section
set_option autoImplicit false
open Set

namespace ENT.Quantitative
noncomputable section

theorem abs_exp_sub_exp_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a-Real.exp b| ≤ |a-b| := by
  have hordered (a b : ℝ) (hab : a ≤ b) (hb : b ≤ 0) :
      |Real.exp a-Real.exp b| ≤ |a-b| := by
    have hdiff : a-b ≤ 0 := by linarith
    have hs := abs_exp_sub_one_le_neg hdiff
    have he : Real.exp a-Real.exp b = Real.exp b*(Real.exp (a-b)-1) := by
      rw [Real.exp_sub]
      field_simp
    rw [he, abs_mul, abs_of_pos (Real.exp_pos b), abs_of_nonpos hdiff]
    calc
      _ ≤ Real.exp b * (-(a-b)) := mul_le_mul_of_nonneg_left hs (Real.exp_pos b).le
      _ ≤ -(a-b) := by
        have h := Real.exp_le_one_iff.mpr hb
        nlinarith
  rcases le_total a b with hab | hba
  · exact hordered a b hab hb
  · simpa only [abs_sub_comm] using hordered b a hba ha

theorem exp_taylor_three_neg {y : ℝ} (hy : y ≤ 0) :
    |Real.exp y-(1+y+y^2/2+y^3/6)| ≤ y^4/24 := by
  by_cases hy0 : y = 0
  · simp [hy0]
  have hi (k : ℕ) : iteratedDeriv k Real.exp = Real.exp := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  have hd (k : ℕ) : iteratedDerivWithin k Real.exp (uIcc 0 y) 0 = 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hy0))
      Real.contDiff_exp.contDiffAt left_mem_uIcc, hi, Real.exp_zero]
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.exp) (n := 3) (Ne.symm hy0) Real.contDiff_exp.contDiffOn
  have hp : taylorWithinEval Real.exp 3 (uIcc 0 y) 0 y = 1+y+y^2/2+y^3/6 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hd, smul_eq_mul]
    ring
  rw [hp, hi] at he
  norm_num at he
  have hz0 : z ≤ 0 := hz.2.le.trans (max_le le_rfl hy)
  have hez : Real.exp z ≤ 1 := Real.exp_le_one_iff.mpr hz0
  have heq : Real.exp y-(1+y+y^2/2+y^3/6) = Real.exp z*y^4/24 := by linarith
  rw [heq, abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hez (show 0 ≤ y^4 by positivity)]

def exponentialThirdProfile (A B C r : ℝ) : ℝ :=
  1-A*r+(A^2/2-B)*r^2+(-C+A*B-A^3/6)*r^3

def exponentialThirdErrorWeight (A B C : ℝ) : ℝ :=
  (A+B+C)^4/24 + (A*C+B^2/2+B*C+C^2/2) +
    (A^2*B/2+(A^2*C+A*B^2)/2+(A*B*C+B^3/6)+
      (A*C^2+B^2*C)/2+B*C^2/2+C^3/6)

theorem exponentialThirdErrorWeight_nonneg {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ exponentialThirdErrorWeight A B C := by
  unfold exponentialThirdErrorWeight
  positivity

theorem exp_third_profile_bound {A B C r : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.exp (-A*r-B*r^2-C*r^3)-exponentialThirdProfile A B C r| ≤
      r^4*exponentialThirdErrorWeight A B C := by
  let q := -A*r-B*r^2-C*r^3
  let Q2 := A*C+B^2/2+B*C*r+C^2/2*r^2
  let Q3 := A^2*B/2+(A^2*C+A*B^2)/2*r+(A*B*C+B^3/6)*r^2+
    (A*C^2+B^2*C)/2*r^3+B*C^2/2*r^4+C^3/6*r^5
  have hq : q ≤ 0 := by
    have hh : 0 ≤ A*r+B*r^2+C*r^3 := by positivity
    dsimp [q]
    linarith
  have hpow (k : ℕ) : r^k ≤ 1 := pow_le_one₀ hr hr1
  have hqabs : |q| ≤ (A+B+C)*r := by
    rw [abs_of_nonpos hq]
    have hr2 : r^2 ≤ r := by nlinarith
    have hr3 : r^3 ≤ r := by nlinarith [mul_le_mul_of_nonneg_left hr2 hr]
    dsimp [q]
    nlinarith [mul_le_mul_of_nonneg_left hr2 hB, mul_le_mul_of_nonneg_left hr3 hC]
  have htaylor : |Real.exp q-(1+q+q^2/2+q^3/6)| ≤ r^4*(A+B+C)^4/24 := by
    refine (exp_taylor_three_neg hq).trans ?_
    have hh := pow_le_pow_left₀ (abs_nonneg q) hqabs 4
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ q^4)] at hh
    nlinarith
  have hQ2 : 0 ≤ Q2 := by dsimp [Q2]; positivity
  have hQ3 : 0 ≤ Q3 := by dsimp [Q3]; positivity
  have hQ2b : Q2 ≤ A*C+B^2/2+B*C+C^2/2 := by
    dsimp [Q2]
    have hh := mul_le_mul_of_nonneg_left (hpow 2) (show 0 ≤ C^2/2 by positivity)
    have hh1 := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hB hC)
    nlinarith
  have hQ3b : Q3 ≤ A^2*B/2+(A^2*C+A*B^2)/2+(A*B*C+B^3/6)+
      (A*C^2+B^2*C)/2+B*C^2/2+C^3/6 := by
    dsimp [Q3]
    have h1 := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ (A^2*C+A*B^2)/2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left (hpow 2) (show 0 ≤ A*B*C+B^3/6 by positivity)
    have h3 := mul_le_mul_of_nonneg_left (hpow 3) (show 0 ≤ (A*C^2+B^2*C)/2 by positivity)
    have h4 := mul_le_mul_of_nonneg_left (hpow 4) (show 0 ≤ B*C^2/2 by positivity)
    have h5 := mul_le_mul_of_nonneg_left (hpow 5) (show 0 ≤ C^3/6 by positivity)
    nlinarith
  have heq : 1+q+q^2/2+q^3/6-exponentialThirdProfile A B C r = r^4*(Q2-Q3) := by
    dsimp [q, Q2, Q3, exponentialThirdProfile]
    ring
  have hrest : |1+q+q^2/2+q^3/6-exponentialThirdProfile A B C r| ≤ r^4*(Q2+Q3) := by
    rw [heq, abs_mul, abs_of_nonneg (pow_nonneg hr 4)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr 4)
    simpa only [abs_of_nonneg hQ2, abs_of_nonneg hQ3] using abs_sub Q2 Q3
  calc
    _ ≤ |Real.exp q-(1+q+q^2/2+q^3/6)|+
        |1+q+q^2/2+q^3/6-exponentialThirdProfile A B C r| := abs_sub_le _ _ _
    _ ≤ r^4*(A+B+C)^4/24+r^4*(Q2+Q3) := add_le_add htaylor hrest
    _ ≤ _ := by
      dsimp [exponentialThirdErrorWeight]
      have hh := mul_le_mul_of_nonneg_left (add_le_add hQ2b hQ3b) (pow_nonneg hr 4)
      nlinarith

def exponentialThirdProfileWeight (A B C : ℝ) : ℝ :=
  1+A+(A^2/2+B)+(C+A*B+A^3/6)

theorem abs_exponentialThirdProfile_le {A B C r : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |exponentialThirdProfile A B C r| ≤ exponentialThirdProfileWeight A B C := by
  have h2 : |A^2/2-B| ≤ A^2/2+B := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg A]
  have h3 : |-C+A*B-A^3/6| ≤ C+A*B+A^3/6 := by
    calc
      _ ≤ |-C+A*B|+|A^3/6| := abs_sub _ _
      _ ≤ (|-C|+|A*B|)+|A^3/6| := add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_neg, abs_of_nonneg hC, abs_of_nonneg (mul_nonneg hA hB), abs_of_nonneg (by positivity : 0 ≤ A^3/6)]
  have h1 : |1-A*r| ≤ 1+A := by
    calc
      _ ≤ |(1:ℝ)|+|A*r| := abs_sub _ _
      _ = 1+A*r := by rw [abs_of_nonneg (by norm_num : 0 ≤ (1:ℝ)), abs_of_nonneg (mul_nonneg hA hr)]
      _ ≤ _ := by nlinarith
  have h22 : |(A^2/2-B)*r^2| ≤ A^2/2+B := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr 2)]
    have hpow := pow_le_one₀ hr hr1 (n := 2)
    nlinarith [mul_le_mul h2 hpow (pow_nonneg hr 2) (show 0 ≤ A^2/2+B by positivity)]
  have h33 : |(-C+A*B-A^3/6)*r^3| ≤ C+A*B+A^3/6 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr 3)]
    have hpow := pow_le_one₀ hr hr1 (n := 3)
    nlinarith [mul_le_mul h3 hpow (pow_nonneg hr 3) (show 0 ≤ C+A*B+A^3/6 by positivity)]
  unfold exponentialThirdProfile exponentialThirdProfileWeight
  calc
    _ ≤ |1-A*r+(A^2/2-B)*r^2|+|(-C+A*B-A^3/6)*r^3| := abs_add_le _ _
    _ ≤ |1-A*r|+|(A^2/2-B)*r^2|+|(-C+A*B-A^3/6)*r^3| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith

end
end ENT.Quantitative
