module

public import ENT.Quantitative.EdgeworthPointwise
public import ENT.Quantitative.FourierEnvelopeMonotone
public import Mathlib.Analysis.Real.Pi.Bounds

/-! An integrable majorant for the first Fourier Edgeworth correction.
The local logarithm bound is proved from its Taylor limit. Outside that
neighborhood the dimension is absorbed into a quadratic frequency weight.
No convergence/integration interchange is assumed. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace ENT.Quantitative
noncomputable section

def SincLogNeighborhood (δ : ℝ) : Prop :=
  ∀ x : ℝ, |x| < δ → 0 < Real.sinc x ∧
    -(x^4) ≤ Real.log (Real.sinc x)+x^2/6 ∧ Real.log (Real.sinc x)+x^2/6 ≤ 0

theorem exists_sincLogNeighborhood : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ SincLogNeighborhood δ := by
  have hgood : ∀ᶠ x : ℝ in 𝓝[≠] 0,
      -1 < (Real.log (Real.sinc x)+x^2/6)/x^4 ∧
      (Real.log (Real.sinc x)+x^2/6)/x^4 < 0 := by
    exact ((tendsto_order.mp log_sinc_taylor_four_limit).1 (-1) (by norm_num)).and
      ((tendsto_order.mp log_sinc_taylor_four_limit).2 0 (by norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hgood
  refine ⟨min ε 1, lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro x hx
  have hx1 : |x| < 1 := hx.trans_le (min_le_right _ _)
  refine ⟨Real.sinc_pos (hx1.trans (by linarith [Real.pi_gt_three])), ?_⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have hg := hball ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
    (hx.trans_le (min_le_left ε 1)), hx0⟩
  have hp : 0 < x^4 := by positivity
  have hlo := (lt_div_iff₀ hp).mp hg.1
  have hhi := (div_lt_iff₀ hp).mp hg.2
  constructor <;> linarith

theorem uniformLogCorrection_eq_scaled {n : ℕ} (hn : 0 < n) (u : ℝ) :
    uniformLogCorrection n u = (n:ℝ)*
      (Real.log (Real.sinc (uniformSumFrequency n u))+(uniformSumFrequency n u)^2/6) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [uniformSumFrequency_sq hn]
  unfold uniformLogCorrection
  field_simp
  ring

theorem uniformFourierFactor_eq_exp_of_pos {n : ℕ} {u : ℝ}
    (hpos : 0 < Real.sinc (uniformSumFrequency n u)) :
    uniformFourierFactor n u = Pang.gaussianWeight u * Real.exp (uniformLogCorrection n u) := by
  unfold uniformFourierFactor Pang.gaussianWeight uniformLogCorrection
  rw [← Real.exp_add]
  rw [show -u^2/2 + ((n:ℝ)*Real.log (Real.sinc (uniformSumFrequency n u))+u^2/2) =
    (n:ℝ)*Real.log (Real.sinc (uniformSumFrequency n u)) by ring,
    Real.exp_natCast_mul, Real.exp_log hpos]

theorem abs_exp_sub_one_le_neg {c : ℝ} (hc : c ≤ 0) : |Real.exp c-1| ≤ -c := by
  have he : Real.exp c ≤ 1 := Real.exp_le_one_iff.mpr hc
  rw [abs_of_nonpos (by linarith : Real.exp c-1 ≤ 0)]
  linarith [Real.add_one_le_exp c]

theorem uniformFourierFactor_first_bound_local {δ : ℝ} (hδ : SincLogNeighborhood δ)
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : |uniformSumFrequency n u| < δ) :
    |(n:ℝ)*(uniformFourierFactor n u-Pang.gaussianWeight u)| ≤
      9*u^4*Pang.gaussianWeight u := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hg : 0 < Pang.gaussianWeight u := Pang.gaussianWeight_pos u
  obtain ⟨hpos, hlo, hhi⟩ := hδ _ hu
  have hcnonpos : uniformLogCorrection n u ≤ 0 := by
    rw [uniformLogCorrection_eq_scaled hn]
    exact mul_nonpos_of_nonneg_of_nonpos hnR.le hhi
  have hc : -(uniformLogCorrection n u) ≤ 9*u^4/(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlo hnR.le
    rw [← uniformLogCorrection_eq_scaled hn] at h
    have he : (n:ℝ)*(uniformSumFrequency n u)^4 = 9*u^4/(n:ℝ) := by
      rw [show (uniformSumFrequency n u)^4 = ((uniformSumFrequency n u)^2)^2 by ring,
        uniformSumFrequency_sq hn]
      field_simp
      ring
    nlinarith
  rw [uniformFourierFactor_eq_exp_of_pos hpos]
  have he : (n:ℝ)*(Pang.gaussianWeight u*Real.exp (uniformLogCorrection n u)-Pang.gaussianWeight u) =
      (n:ℝ)*Pang.gaussianWeight u*(Real.exp (uniformLogCorrection n u)-1) := by ring
  rw [he, abs_mul, abs_of_pos (mul_pos hnR (Pang.gaussianWeight_pos u))]
  calc
    _ ≤ ((n:ℝ)*Pang.gaussianWeight u)*(-uniformLogCorrection n u) :=
      mul_le_mul_of_nonneg_left (abs_exp_sub_one_le_neg hcnonpos) (by positivity)
    _ ≤ ((n:ℝ)*Pang.gaussianWeight u)*(9*u^4/(n:ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by field_simp

theorem uniformFourierFactor_abs_le_fixed {N n : ℕ} (hN : 0 < N) (hNn : N ≤ n) (u : ℝ) :
    |uniformFourierFactor n u| ≤ Pang.pangEnvelope N u := by
  have hn : 0 < n := hN.trans_le hNn
  have h := (norm_charFun_standardizedDiagonal_le hn u).trans
    (fourier_envelope_le_fixed hN hNn u)
  have hnR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hp : (1+u^2/(N:ℝ))^(-(N:ℝ)/2) ≤ Pang.pangEnvelope N u := by
    apply Real.rpow_le_rpow_of_exponent_le
    · have h : 0 ≤ u^2/(N:ℝ) := by positivity
      linarith
    · linarith
  have he : ‖charFun (standardizedProjectionLaw (diagonal n)) u‖ = |uniformFourierFactor n u| := by
    rw [charFun_standardizedDiagonal, uniformFourierFactor, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_pow]
  rw [he] at h
  exact h.trans hp

def firstFourierMajorant (δ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  9*u^4*Pang.gaussianWeight u +
    (3/δ^2)*u^2*(Pang.pangEnvelope N u+Pang.gaussianWeight u)

theorem uniformFourierFactor_first_bound {δ : ℝ} (hδ0 : 0 < δ) (hδ : SincLogNeighborhood δ)
    {N n : ℕ} (hN : 0 < N) (hNn : N ≤ n) (u : ℝ) :
    |(n:ℝ)*(uniformFourierFactor n u-Pang.gaussianWeight u)| ≤ firstFourierMajorant δ N u := by
  have hn : 0 < n := hN.trans_le hNn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hp : 0 < Pang.pangEnvelope N u := Pang.pangEnvelope_pos hN u
  have hg : 0 < Pang.gaussianWeight u := Pang.gaussianWeight_pos u
  by_cases hlocal : |uniformSumFrequency n u| < δ
  · exact (uniformFourierFactor_first_bound_local hδ hn hlocal).trans
      (by unfold firstFourierMajorant; exact le_add_of_nonneg_right (by positivity))
  have hfreq : δ ≤ |uniformSumFrequency n u| := le_of_not_gt hlocal
  have hsq := pow_le_pow_left₀ hδ0.le hfreq 2
  rw [sq_abs, uniformSumFrequency_sq hn] at hsq
  have hdim : (n:ℝ) ≤ (3/δ^2)*u^2 := by
    have hδsq : 0 < δ^2 := sq_pos_of_pos hδ0
    have hb := (le_div_iff₀ hnR).mp hsq
    have hh : (n:ℝ) ≤ 3*u^2/δ^2 := (le_div_iff₀ hδsq).mpr (by nlinarith)
    convert hh using 1 <;> ring
  rw [abs_mul, abs_of_pos hnR]
  calc
    _ ≤ (n:ℝ)*(|uniformFourierFactor n u|+Pang.gaussianWeight u) := by
      apply mul_le_mul_of_nonneg_left _ hnR.le
      simpa only [abs_of_pos hg] using abs_sub (uniformFourierFactor n u) (Pang.gaussianWeight u)
    _ ≤ ((3/δ^2)*u^2)*(Pang.pangEnvelope N u+Pang.gaussianWeight u) := by
      have hs : |uniformFourierFactor n u|+Pang.gaussianWeight u ≤
          Pang.pangEnvelope N u+Pang.gaussianWeight u := by
        linarith [uniformFourierFactor_abs_le_fixed hN hNn u]
      exact mul_le_mul hdim hs (by positivity) (by positivity)
    _ ≤ _ := by unfold firstFourierMajorant; exact le_add_of_nonneg_left (by positivity)

theorem integrable_abs_pow_gaussianWeight (k : ℕ) :
    Integrable (fun u : ℝ => |u|^k*Pang.gaussianWeight u) := by
  have h := (Pang.integrable_pow_mul_gaussianWeight k).norm
  simpa only [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos (Pang.gaussianWeight_pos _)] using h

theorem integrable_firstFourierMajorant_weighted {N k : ℕ} (hN : k+4 < N) (δ : ℝ) :
    Integrable (fun u : ℝ => |u|^k*firstFourierMajorant δ N u) := by
  have hg4 := (integrable_abs_pow_gaussianWeight (k+4)).const_mul 9
  have he2 := Pang.integrable_abs_pow_mul_pangEnvelope (n := N) (k := k+2) (by omega)
  have hg2 := integrable_abs_pow_gaussianWeight (k+2)
  have hi := hg4.fun_add ((he2.fun_add hg2).const_mul (3/δ^2))
  convert hi using 1
  funext u
  unfold firstFourierMajorant
  rw [pow_add, pow_add]
  have h4 : |u|^4 = u^4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [h4, sq_abs]
  ring

end
end ENT.Quantitative
