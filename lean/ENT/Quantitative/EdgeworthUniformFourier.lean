module

public import ENT.Quantitative.EdgeworthLogExpansion
public import ENT.Quantitative.EdgeworthExponential
public import ENT.Quantitative.EdgeworthPolynomials

/-! A global integrable O(n⁻⁴) error for the actual characteristic function
of the standardized uniform sum and its three-term Edgeworth profile. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory Polynomial
open scoped Topology

namespace ENT.Quantitative
noncomputable section

def uniformCumulantA (u : ℝ) : ℝ := u^4/20
def uniformCumulantB (u : ℝ) : ℝ := u^6/105
def uniformCumulantC (u : ℝ) : ℝ := 3*u^8/1400

def uniformCumulantTruncation (n : ℕ) (u : ℝ) : ℝ :=
  -uniformCumulantA u/(n:ℝ)-uniformCumulantB u/(n:ℝ)^2-uniformCumulantC u/(n:ℝ)^3

def uniformFourierProfile (n : ℕ) (u : ℝ) : ℝ :=
  Pang.gaussianWeight u * exponentialThirdProfile
    (uniformCumulantA u) (uniformCumulantB u) (uniformCumulantC u) (n:ℝ)⁻¹

def uniformFourierLocalWeight (C : ℝ) (u : ℝ) : ℝ :=
  243*C*u^10+exponentialThirdErrorWeight (uniformCumulantA u) (uniformCumulantB u) (uniformCumulantC u)

def uniformFourierProfileWeight (u : ℝ) : ℝ :=
  exponentialThirdProfileWeight (uniformCumulantA u) (uniformCumulantB u) (uniformCumulantC u)

def uniformFourierMajorant (C δ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  uniformFourierLocalWeight C u*Pang.gaussianWeight u+
    (3/δ^2)^4*u^8*(Pang.pangEnvelope N u+Pang.gaussianWeight u*uniformFourierProfileWeight u)

theorem uniformCumulantA_nonneg (u : ℝ) : 0 ≤ uniformCumulantA u := by unfold uniformCumulantA; positivity
theorem uniformCumulantB_nonneg (u : ℝ) : 0 ≤ uniformCumulantB u := by unfold uniformCumulantB; positivity
theorem uniformCumulantC_nonneg (u : ℝ) : 0 ≤ uniformCumulantC u := by unfold uniformCumulantC; positivity

theorem uniformLogCorrection_sub_cumulant {n : ℕ} (hn : 0 < n) (u : ℝ) :
    uniformLogCorrection n u-uniformCumulantTruncation n u =
      (n:ℝ)*(Real.log (Real.sinc (uniformSumFrequency n u))-logSincEighth (uniformSumFrequency n u)) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [uniformLogCorrection_eq_scaled hn]
  unfold uniformCumulantTruncation logSincEighth uniformCumulantA uniformCumulantB uniformCumulantC
  rw [show (uniformSumFrequency n u)^4 = ((uniformSumFrequency n u)^2)^2 by ring,
    show (uniformSumFrequency n u)^6 = ((uniformSumFrequency n u)^2)^3 by ring,
    show (uniformSumFrequency n u)^8 = ((uniformSumFrequency n u)^2)^4 by ring,
    uniformSumFrequency_sq hn]
  field_simp
  ring

theorem uniformCumulantTruncation_nonpos (n : ℕ) (u : ℝ) : uniformCumulantTruncation n u ≤ 0 := by
  have h : 0 ≤ uniformCumulantA u/(n:ℝ)+uniformCumulantB u/(n:ℝ)^2+uniformCumulantC u/(n:ℝ)^3 := by
    have := uniformCumulantA_nonneg u
    have := uniformCumulantB_nonneg u
    have := uniformCumulantC_nonneg u
    positivity
  unfold uniformCumulantTruncation
  convert neg_nonpos.mpr h using 1 <;> ring

theorem uniformFourierProfile_bound {n : ℕ} (hn : 0 < n) (u : ℝ) :
    |uniformFourierProfile n u| ≤ Pang.gaussianWeight u*uniformFourierProfileWeight u := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hi : (n:ℝ)⁻¹ ≤ 1 := by exact (inv_le_one₀ (by positivity : 0 < (n:ℝ))).mpr hn1
  rw [uniformFourierProfile, abs_mul, abs_of_pos (Pang.gaussianWeight_pos u)]
  exact mul_le_mul_of_nonneg_left (abs_exponentialThirdProfile_le
    (uniformCumulantA_nonneg u) (uniformCumulantB_nonneg u) (uniformCumulantC_nonneg u)
    (by positivity) hi) (Pang.gaussianWeight_pos u).le

theorem uniformFourierFactor_third_bound_local {C δ : ℝ} (hC : 0 ≤ C)
    (hδ : SincLogNeighborhood δ)
    (hlog : ∀ x : ℝ, |x| < δ → |Real.log (Real.sinc x)-logSincEighth x| ≤ C*x^10)
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : |uniformSumFrequency n u| < δ) :
    |(n:ℝ)^4*(uniformFourierFactor n u-uniformFourierProfile n u)| ≤
      uniformFourierLocalWeight C u*Pang.gaussianWeight u := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hi : (n:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hnR).mpr hn1
  obtain ⟨hpos, hlo, hhi⟩ := hδ _ hu
  have hc : uniformLogCorrection n u ≤ 0 := by
    rw [uniformLogCorrection_eq_scaled hn]
    exact mul_nonpos_of_nonneg_of_nonpos hnR.le hhi
  have hdiff : |uniformLogCorrection n u-uniformCumulantTruncation n u| ≤
      243*C*u^10/(n:ℝ)^4 := by
    rw [uniformLogCorrection_sub_cumulant hn, abs_mul, abs_of_pos hnR]
    have hh := mul_le_mul_of_nonneg_left (hlog _ hu) hnR.le
    convert hh using 1
    rw [show (uniformSumFrequency n u)^10 = ((uniformSumFrequency n u)^2)^5 by ring,
      uniformSumFrequency_sq hn]
    field_simp
    ring
  have he1 := (abs_exp_sub_exp_le_of_nonpos hc (uniformCumulantTruncation_nonpos n u)).trans hdiff
  have he2 : |Real.exp (uniformCumulantTruncation n u)-
      exponentialThirdProfile (uniformCumulantA u) (uniformCumulantB u) (uniformCumulantC u) (n:ℝ)⁻¹| ≤
      exponentialThirdErrorWeight (uniformCumulantA u) (uniformCumulantB u) (uniformCumulantC u)/(n:ℝ)^4 := by
    have hh := exp_third_profile_bound (uniformCumulantA_nonneg u) (uniformCumulantB_nonneg u)
      (uniformCumulantC_nonneg u) (show 0 ≤ (n:ℝ)⁻¹ by positivity) hi
    simpa only [uniformCumulantTruncation, div_eq_mul_inv, inv_pow, mul_comm] using hh
  have he : |Real.exp (uniformLogCorrection n u)-
      exponentialThirdProfile (uniformCumulantA u) (uniformCumulantB u) (uniformCumulantC u) (n:ℝ)⁻¹| ≤
      uniformFourierLocalWeight C u/(n:ℝ)^4 := by
    calc
      _ ≤ |Real.exp (uniformLogCorrection n u)-Real.exp (uniformCumulantTruncation n u)|+
          |Real.exp (uniformCumulantTruncation n u)-exponentialThirdProfile
            (uniformCumulantA u) (uniformCumulantB u) (uniformCumulantC u) (n:ℝ)⁻¹| := abs_sub_le _ _ _
      _ ≤ _ := by
        unfold uniformFourierLocalWeight
        rw [add_div]
        exact add_le_add he1 he2
  rw [uniformFourierFactor_eq_exp_of_pos hpos, uniformFourierProfile,
    show (n:ℝ)^4*(Pang.gaussianWeight u*Real.exp (uniformLogCorrection n u)-
      Pang.gaussianWeight u*exponentialThirdProfile (uniformCumulantA u) (uniformCumulantB u)
        (uniformCumulantC u) (n:ℝ)⁻¹) = (n:ℝ)^4*Pang.gaussianWeight u*
      (Real.exp (uniformLogCorrection n u)-exponentialThirdProfile (uniformCumulantA u)
        (uniformCumulantB u) (uniformCumulantC u) (n:ℝ)⁻¹) by ring,
    abs_mul, abs_of_pos (mul_pos (by positivity) (Pang.gaussianWeight_pos u))]
  calc
    _ ≤ ((n:ℝ)^4*Pang.gaussianWeight u)*(uniformFourierLocalWeight C u/(n:ℝ)^4) :=
      mul_le_mul_of_nonneg_left he (by have := Pang.gaussianWeight_pos u; positivity)
    _ = _ := by field_simp

theorem uniformFourierFactor_third_bound {C δ : ℝ} (hC : 0 ≤ C) (hδ0 : 0 < δ)
    (hδ : SincLogNeighborhood δ)
    (hlog : ∀ x : ℝ, |x| < δ → |Real.log (Real.sinc x)-logSincEighth x| ≤ C*x^10)
    {N n : ℕ} (hN : 0 < N) (hNn : N ≤ n) (u : ℝ) :
    |(n:ℝ)^4*(uniformFourierFactor n u-uniformFourierProfile n u)| ≤ uniformFourierMajorant C δ N u := by
  have hn : 0 < n := hN.trans_le hNn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hp := Pang.pangEnvelope_pos hN u
  have hg := Pang.gaussianWeight_pos u
  have hP : 0 ≤ uniformFourierProfileWeight u := by
    unfold uniformFourierProfileWeight exponentialThirdProfileWeight
    have := uniformCumulantA_nonneg u
    have := uniformCumulantB_nonneg u
    have := uniformCumulantC_nonneg u
    positivity
  have hL : 0 ≤ uniformFourierLocalWeight C u := by
    unfold uniformFourierLocalWeight
    have := exponentialThirdErrorWeight_nonneg (uniformCumulantA_nonneg u)
      (uniformCumulantB_nonneg u) (uniformCumulantC_nonneg u)
    positivity
  by_cases hlocal : |uniformSumFrequency n u| < δ
  · exact (uniformFourierFactor_third_bound_local hC hδ hlog hn hlocal).trans
      (by unfold uniformFourierMajorant; exact le_add_of_nonneg_right (by positivity))
  have hfreq : δ ≤ |uniformSumFrequency n u| := le_of_not_gt hlocal
  have hsq := pow_le_pow_left₀ hδ0.le hfreq 2
  rw [sq_abs, uniformSumFrequency_sq hn] at hsq
  have hdim : (n:ℝ) ≤ (3/δ^2)*u^2 := by
    have hδsq : 0 < δ^2 := sq_pos_of_pos hδ0
    have hb := (le_div_iff₀ hnR).mp hsq
    have hh : (n:ℝ) ≤ 3*u^2/δ^2 := (le_div_iff₀ hδsq).mpr (by nlinarith)
    convert hh using 1 <;> ring
  have hdim4 : (n:ℝ)^4 ≤ (3/δ^2)^4*u^8 := by
    convert pow_le_pow_left₀ hnR.le hdim 4 using 1 <;> ring
  rw [abs_mul, abs_of_pos (by positivity : 0 < (n:ℝ)^4)]
  calc
    _ ≤ (n:ℝ)^4*(|uniformFourierFactor n u|+|uniformFourierProfile n u|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    _ ≤ ((3/δ^2)^4*u^8)*(Pang.pangEnvelope N u+Pang.gaussianWeight u*uniformFourierProfileWeight u) := by
      exact mul_le_mul hdim4 (add_le_add (uniformFourierFactor_abs_le_fixed hN hNn u)
        (uniformFourierProfile_bound hn u)) (by positivity) (by positivity)
    _ ≤ _ := by unfold uniformFourierMajorant; exact le_add_of_nonneg_left (by positivity)

private def uniformFourierGaussianPolynomial (K δ : ℝ) : ℝ[X] :=
  let A : ℝ[X] := C (1/20)*X^2
  let B : ℝ[X] := C (1/105)*X^3
  let D : ℝ[X] := C (3/1400)*X^4
  C (243*K)*X^5 + C (1/24)*(A+B+D)^4 +
    (A*D+C (1/2)*B^2+B*D+C (1/2)*D^2) +
    (C (1/2)*A^2*B+C (1/2)*(A^2*D+A*B^2)+(A*B*D+C (1/6)*B^3)+
      C (1/2)*(A*D^2+B^2*D)+C (1/2)*B*D^2+C (1/6)*D^3) +
    C ((3/δ^2)^4)*X^4*(1+A+(C (1/2)*A^2+B)+(D+A*B+C (1/6)*A^3))

private theorem uniformFourierGaussianPolynomial_eval (K δ u : ℝ) :
    (uniformFourierGaussianPolynomial K δ).eval (u^2) =
      uniformFourierLocalWeight K u+(3/δ^2)^4*u^8*uniformFourierProfileWeight u := by
  simp only [uniformFourierGaussianPolynomial, uniformFourierLocalWeight,
    uniformFourierProfileWeight, exponentialThirdErrorWeight, exponentialThirdProfileWeight,
    uniformCumulantA, uniformCumulantB, uniformCumulantC, eval_add, eval_mul, eval_pow,
    eval_C, eval_X, eval_one]
  ring

theorem integrable_evenPolynomial_gaussianWeight (p : ℝ[X]) :
    Integrable (fun u : ℝ => p.eval (u^2)*Pang.gaussianWeight u) := by
  have hs : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
  have hi := (integrable_evenPolynomial_gaussian p).const_mul (Real.sqrt (2*Real.pi))
  convert hi using 1
  funext u
  rw [standardGaussianPDF_eq]
  field_simp

theorem integrable_uniformFourierMajorant {N : ℕ} (hN : 10 < N) (C δ : ℝ) :
    Integrable (uniformFourierMajorant C δ N) := by
  have hp := integrable_evenPolynomial_gaussianWeight (uniformFourierGaussianPolynomial C δ)
  have he := (Pang.integrable_abs_pow_mul_pangEnvelope (n := N) (k := 8) (by omega)).const_mul ((3/δ^2)^4)
  have hi := hp.fun_add he
  convert hi using 1
  funext u
  rw [uniformFourierGaussianPolynomial_eval]
  have h8 : |u|^8 = u^8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [h8]
  unfold uniformFourierMajorant
  ring

end
end ENT.Quantitative
