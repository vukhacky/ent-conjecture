module

public import ENT.Quantitative.EdgeworthFourierBounds
public import Mathlib.Algebra.Polynomial.Div

/-! The order-eight expansion of the logarithm of sinc near zero. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory Polynomial
open scoped Topology

namespace ENT.Quantitative
noncomputable section

def sincTruncation (y : ℝ) : ℝ := -y/6+y^2/120-y^3/5040+y^4/362880

def logFourthTruncation (z : ℝ) : ℝ := z-z^2/2+z^3/3-z^4/4

def logSincEighth (x : ℝ) : ℝ := -x^2/6-x^4/180-x^6/2835-x^8/37800

private def logSincPolynomialQuotient : ℝ[X] :=
  Polynomial.C (-1/69360485251091005440000:ℝ)*Polynomial.X^11 +
  Polynomial.C (1/240835018232954880000:ℝ)*Polynomial.X^10 +
  Polynomial.C (-1/1605566788219699200:ℝ)*Polynomial.X^9 +
  Polynomial.C (629/10034792426373120000:ℝ)*Polynomial.X^8 +
  Polynomial.C (-11633/2508698106593280000:ℝ)*Polynomial.X^7 +
  Polynomial.C (437/1659191869440000:ℝ)*Polynomial.X^6 +
  Polynomial.C (-647/55306395648000:ℝ)*Polynomial.X^5 +
  Polynomial.C (56291/138265989120000:ℝ)*Polynomial.X^4 +
  Polynomial.C (-72103/6584094720000:ℝ)*Polynomial.X^3 +
  Polynomial.C (6023/27433728000:ℝ)*Polynomial.X^2 +
  Polynomial.C (-13873/4572288000:ℝ)*Polynomial.X^1 +
  Polynomial.C (257/10886400:ℝ)

private theorem logSincPolynomialQuotient_identity (x : ℝ) :
    logFourthTruncation (sincTruncation (x^2)) - logSincEighth x =
      x^10 * logSincPolynomialQuotient.eval (x^2) := by
  simp only [logFourthTruncation, sincTruncation, logSincEighth,
    logSincPolynomialQuotient, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem sin_taylor_eleven_remainder :
    Tendsto (fun x : ℝ => (Real.sin x -
      (x-x^3/6+x^5/120-x^7/5040+x^9/362880-x^11/39916800))/x^11)
      (𝓝 0) (𝓝 0) := by
  have hp (x : ℝ) : taylorWithinEval Real.sin 11 univ 0 x =
      x-x^3/6+x^5/120-x^7/5040+x^9/362880-x^11/39916800 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, iteratedDerivWithin_univ,
      show (2:ℕ) = 1+1 from rfl, show (3:ℕ) = 2+1 from rfl,
      show (4:ℕ) = 3+1 from rfl, show (5:ℕ) = 4+1 from rfl,
      show (6:ℕ) = 5+1 from rfl, show (7:ℕ) = 6+1 from rfl,
      show (8:ℕ) = 7+1 from rfl, show (9:ℕ) = 8+1 from rfl,
      show (10:ℕ) = 9+1 from rfl, show (11:ℕ) = 10+1 from rfl]
    ring
  have h := (taylor_isLittleO_univ (f := Real.sin) (n := 11) (x₀ := 0)
    Real.contDiff_sin).tendsto_div_nhds_zero
  simpa only [hp, sub_zero] using h

theorem sinc_taylor_ten_limit :
    Tendsto (fun x : ℝ => (Real.sinc x-1-sincTruncation (x^2))/x^10)
      (𝓝[≠] 0) (𝓝 (-1/39916800:ℝ)) := by
  have ht := (sin_taylor_eleven_remainder.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)).sub_const (1/39916800:ℝ)
  norm_num at ht ⊢
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  rw [Real.sinc_of_ne_zero hx0]
  unfold sincTruncation
  field_simp
  ring

private def logFourthDifferenceFactor (s t : ℝ) : ℝ :=
  1-(s+t)/2+(s^2+s*t+t^2)/3-(s^3+s^2*t+s*t^2+t^3)/4

private theorem logFourthTruncation_sub (s t : ℝ) :
    logFourthTruncation s-logFourthTruncation t = (s-t)*logFourthDifferenceFactor s t := by
  unfold logFourthTruncation logFourthDifferenceFactor
  ring

private theorem logFourthTruncation_error {z : ℝ} (hz : |z| ≤ 1/2) :
    |Real.log (1+z)-logFourthTruncation z| ≤ 2*|z|^5 := by
  have hz1 : |z| < 1 := by linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := -z) (by simpa using hz1) 4
  norm_num [Finset.sum_range_succ] at h
  have he : -z+z^2/2+(-z)^3/3+z^4/4+Real.log (1+z) =
      Real.log (1+z)-logFourthTruncation z := by unfold logFourthTruncation; ring
  rw [he] at h
  refine h.trans ?_
  apply (div_le_iff₀ (by linarith : 0 < 1-|z|)).mpr
  nlinarith [pow_nonneg (abs_nonneg z) 5]

theorem exists_logSincEighth_bound :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧ SincLogNeighborhood δ ∧
      ∀ x : ℝ, |x| < δ → |Real.log (Real.sinc x)-logSincEighth x| ≤ C*x^10 := by
  have hs : Tendsto (fun x : ℝ => Real.sinc x-1) (𝓝 0) (𝓝 (0:ℝ)) := by
    simpa using (Real.continuous_sinc.tendsto (0:ℝ)).sub_const 1
  have ht : Tendsto (fun x : ℝ => sincTruncation (x^2)) (𝓝 0) (𝓝 (0:ℝ)) := by
    have hc : Continuous (fun x : ℝ => sincTruncation (x^2)) := by
      unfold sincTruncation
      fun_prop
    simpa [sincTruncation] using hc.tendsto (0:ℝ)
  have hf : Tendsto (fun x : ℝ =>
      logFourthDifferenceFactor (Real.sinc x-1) (sincTruncation (x^2))) (𝓝 0) (𝓝 (1:ℝ)) := by
    have hc : Continuous (fun p : ℝ × ℝ => logFourthDifferenceFactor p.1 p.2) := by
      unfold logFourthDifferenceFactor
      fun_prop
    have hh := (hc.tendsto (0,0)).comp (hs.prodMk_nhds ht)
    simpa [logFourthDifferenceFactor, Function.comp_def] using hh
  let Q := logSincPolynomialQuotient
  have hq : Tendsto (fun x : ℝ => |Q.eval (x^2)|) (𝓝 0) (𝓝 |Q.eval 0|) := by
    have hc : Continuous (fun x : ℝ => |Q.eval (x^2)|) := by fun_prop
    simpa using hc.tendsto (0:ℝ)
  have hg1 : ∀ᶠ x : ℝ in 𝓝[≠] 0,
      |(Real.sinc x-1-sincTruncation (x^2))/x^10| ≤ 1 := by
    have hh := (tendsto_order.mp sinc_taylor_ten_limit.abs).2 (1:ℝ) (by norm_num)
    exact hh.mono fun x hx => hx.le
  have hg2 : ∀ᶠ x : ℝ in 𝓝[≠] 0, |(Real.sinc x-1)/x^2| ≤ 1 := by
    have hh := (tendsto_order.mp sinc_taylor_two_limit.abs).2 (1:ℝ) (by norm_num)
    exact hh.mono fun x hx => hx.le
  have hg3 : ∀ᶠ x : ℝ in 𝓝 0, |Real.sinc x-1| ≤ 1/2 := by
    have hh := (tendsto_order.mp hs.abs).2 (1/2:ℝ) (by norm_num)
    exact hh.mono fun x hx => hx.le
  have hg4 : ∀ᶠ x : ℝ in 𝓝 0,
      |logFourthDifferenceFactor (Real.sinc x-1) (sincTruncation (x^2))| ≤ 2 := by
    have hh := (tendsto_order.mp hf.abs).2 (2:ℝ) (by norm_num)
    exact hh.mono fun x hx => hx.le
  have hg5 : ∀ᶠ x : ℝ in 𝓝 0, |Q.eval (x^2)| ≤ |Q.eval 0|+1 := by
    exact ((tendsto_order.mp hq).2 _ (by linarith)).mono fun x hx => hx.le
  have hgood : ∀ᶠ x : ℝ in 𝓝[≠] 0,
      |Real.log (Real.sinc x)-logSincEighth x| ≤ (5+|Q.eval 0|)*x^10 := by
    filter_upwards [hg1, hg2, hg3.filter_mono nhdsWithin_le_nhds,
      hg4.filter_mono nhdsWithin_le_nhds, hg5.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with x h1 h2 h3 h4 h5 hx
    have hx0 : x ≠ 0 := hx
    have hx10 : 0 < x^10 := by positivity
    have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx0
    have hsbound : |Real.sinc x-1| ≤ x^2 := by
      rw [abs_div, abs_of_pos hx2] at h2
      simpa only [one_mul] using (div_le_iff₀ hx2).mp h2
    have htrunc : |Real.sinc x-1-sincTruncation (x^2)| ≤ x^10 := by
      rw [abs_div, abs_of_pos hx10] at h1
      simpa only [one_mul] using (div_le_iff₀ hx10).mp h1
    have hlog : |Real.log (Real.sinc x)-logFourthTruncation (Real.sinc x-1)| ≤ 2*x^10 := by
      have hh := logFourthTruncation_error h3
      rw [show 1+(Real.sinc x-1) = Real.sinc x by ring] at hh
      refine hh.trans ?_
      have hhpow := pow_le_pow_left₀ (abs_nonneg (Real.sinc x-1)) hsbound 5
      nlinarith
    have hpoly : |logFourthTruncation (Real.sinc x-1)-
        logFourthTruncation (sincTruncation (x^2))| ≤ 2*x^10 := by
      rw [logFourthTruncation_sub, abs_mul]
      nlinarith [mul_le_mul htrunc h4 (abs_nonneg _) hx10.le]
    have hlast : |logFourthTruncation (sincTruncation (x^2))-logSincEighth x| ≤
        x^10*(|Q.eval 0|+1) := by
      rw [logSincPolynomialQuotient_identity, abs_mul, abs_of_pos hx10]
      exact mul_le_mul_of_nonneg_left h5 hx10.le
    calc
      _ ≤ |Real.log (Real.sinc x)-logFourthTruncation (Real.sinc x-1)| +
          |logFourthTruncation (Real.sinc x-1)-logFourthTruncation (sincTruncation (x^2))| +
          |logFourthTruncation (sincTruncation (x^2))-logSincEighth x| := by
        calc
          _ ≤ |Real.log (Real.sinc x)-logFourthTruncation (Real.sinc x-1)| +
              |logFourthTruncation (Real.sinc x-1)-logSincEighth x| := abs_sub_le _ _ _
          _ ≤ _ := by
            have hh := abs_sub_le (logFourthTruncation (Real.sinc x-1)) (logFourthTruncation (sincTruncation (x^2))) (logSincEighth x)
            linarith
      _ ≤ _ := by nlinarith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hgood
  obtain ⟨δ, hδ, hδ1, hd⟩ := exists_sincLogNeighborhood
  refine ⟨5+|Q.eval 0|, min ε δ, by positivity, lt_min hε hδ,
    (min_le_right _ _).trans hδ1, ?_, ?_⟩
  · intro x hx
    exact hd x (hx.trans_le (min_le_right _ _))
  · intro x hx
    by_cases hx0 : x = 0
    · simp [hx0, logSincEighth]
    exact hball ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      (hx.trans_le (min_le_left _ _)), hx0⟩

end
end ENT.Quantitative
