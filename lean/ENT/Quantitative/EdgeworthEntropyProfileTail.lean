module

public import ENT.Quantitative.EdgeworthEntropyProfile
public import ENT.Quantitative.EntropyExpansionTail

/-! Polynomial control of the relative Edgeworth profile and its cubic
entropy tail on the same expanding central region as the actual density. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory ProbabilityTheory Polynomial
open scoped Topology

namespace ENT.Quantitative
noncomputable section

def profileMajorantPolynomial : ℝ[X] :=
  C 3+uniformEdgeworthA^2+uniformEdgeworthB^2+uniformEdgeworthC^2

theorem profileMajorantPolynomial_nonneg (x : ℝ) :
    0 ≤ profileMajorantPolynomial.eval (x^2) := by
  simp only [profileMajorantPolynomial, eval_add, eval_C, eval_pow]
  positivity

private theorem abs_le_sq_add_one (a : ℝ) : |a| ≤ a^2+1 := by
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (a-1/2), sq_nonneg (a+1/2)]

theorem profile_coefficients_abs_le_majorant (x : ℝ) :
    |uniformEdgeworthA.eval (x^2)|+|uniformEdgeworthB.eval (x^2)|+|uniformEdgeworthC.eval (x^2)| ≤
      profileMajorantPolynomial.eval (x^2) := by
  simp only [profileMajorantPolynomial, eval_add, eval_C, eval_pow]
  linarith [abs_le_sq_add_one (uniformEdgeworthA.eval (x^2)),
    abs_le_sq_add_one (uniformEdgeworthB.eval (x^2)), abs_le_sq_add_one (uniformEdgeworthC.eval (x^2))]

theorem profile_abs_le_majorant {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |uniformEdgeworthRelativeProfile n x| ≤ profileMajorantPolynomial.eval (x^2)/(n:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hr : 0 ≤ (n:ℝ)⁻¹ := by positivity
  have hr1 : (n:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hnR).mpr hn1
  have hr2 : (n:ℝ)⁻¹^2 ≤ (n:ℝ)⁻¹ := by nlinarith
  have hr3 : (n:ℝ)⁻¹^3 ≤ (n:ℝ)⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_left hr2 hr]
  have he : uniformEdgeworthRelativeProfile n x =
      uniformEdgeworthA.eval (x^2)*(n:ℝ)⁻¹+
      uniformEdgeworthB.eval (x^2)*(n:ℝ)⁻¹^2+
      uniformEdgeworthC.eval (x^2)*(n:ℝ)⁻¹^3 := by
    simp only [uniformEdgeworthRelativeProfile, div_eq_mul_inv, inv_pow]
  rw [he]
  calc
    _ ≤ |uniformEdgeworthA.eval (x^2)*(n:ℝ)⁻¹|+
        |uniformEdgeworthB.eval (x^2)*(n:ℝ)⁻¹^2|+
        |uniformEdgeworthC.eval (x^2)*(n:ℝ)⁻¹^3| := by
      calc
        _ ≤ |uniformEdgeworthA.eval (x^2)*(n:ℝ)⁻¹+uniformEdgeworthB.eval (x^2)*(n:ℝ)⁻¹^2|+
            |uniformEdgeworthC.eval (x^2)*(n:ℝ)⁻¹^3| := abs_add_le _ _
        _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
    _ = |uniformEdgeworthA.eval (x^2)| *(n:ℝ)⁻¹+
        |uniformEdgeworthB.eval (x^2)| *(n:ℝ)⁻¹^2+
        |uniformEdgeworthC.eval (x^2)| *(n:ℝ)⁻¹^3 := by
      simp only [abs_mul, abs_of_nonneg hr, abs_of_nonneg (pow_nonneg hr 2),
        abs_of_nonneg (pow_nonneg hr 3)]
    _ ≤ (|uniformEdgeworthA.eval (x^2)|+|uniformEdgeworthB.eval (x^2)|+
        |uniformEdgeworthC.eval (x^2)|)*(n:ℝ)⁻¹ := by
      nlinarith [mul_le_mul_of_nonneg_left hr2 (abs_nonneg (uniformEdgeworthB.eval (x^2))),
        mul_le_mul_of_nonneg_left hr3 (abs_nonneg (uniformEdgeworthC.eval (x^2)))]
    _ ≤ _ := by
      simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right (profile_coefficients_abs_le_majorant x) hr

def entropyProfileTailPolynomial : ℝ[X] :=
  (Real.sqrt (2*Real.pi))⁻¹ • ((1/2:ℝ) • profileMajorantPolynomial^2+
    (1/6:ℝ) • profileMajorantPolynomial^3)

private theorem entropyProfileTailPolynomial_nonneg (x : ℝ) :
    0 ≤ entropyProfileTailPolynomial.eval (x^2) := by
  simp only [entropyProfileTailPolynomial, eval_smul, eval_add, eval_pow, smul_eq_mul]
  have := profileMajorantPolynomial_nonneg x
  positivity

theorem uniformEdgeworthEntropyProfile_gaussian_bound {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |uniformEdgeworthEntropyProfile n x| ≤
      entropyProfileTailPolynomial.eval (x^2)*Real.exp (-(1/2:ℝ)*x^2) := by
  let d := uniformEdgeworthRelativeProfile n x
  let P := profileMajorantPolynomial.eval (x^2)
  have hP : 0 ≤ P := profileMajorantPolynomial_nonneg x
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hd : |d| ≤ P := by
    have h := profile_abs_le_majorant hn x
    exact h.trans (div_le_self hP hn1)
  have hd2 : |d|^2 ≤ P^2 := pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hd3 : |d|^3 ≤ P^3 := pow_le_pow_left₀ (abs_nonneg d) hd 3
  have hφ : 0 < gaussianPDFReal 0 1 x := gaussianPDFReal_pos 0 1 x (by norm_num)
  have hb : |d^2/2-d^3/6| ≤ P^2/2+P^3/6 := by
    calc
      _ ≤ |d^2/2|+|d^3/6| := abs_sub _ _
      _ ≤ _ := by
        simp only [abs_div, abs_pow, abs_of_pos (by norm_num : (0:ℝ)<2),
          abs_of_pos (by norm_num : (0:ℝ)<6)]
        linarith
  rw [uniformEdgeworthEntropyProfile, abs_mul, abs_of_pos hφ]
  have hh := mul_le_mul_of_nonneg_left hb hφ.le
  apply hh.trans_eq
  simp only [entropyProfileTailPolynomial, eval_smul, eval_add, eval_pow, smul_eq_mul]
  rw [standardGaussianPDF_eq]
  unfold Pang.gaussianWeight
  dsimp [P]
  rw [show -x^2/2 = -(1/2:ℝ)*x^2 by ring]
  ring

theorem uniformEdgeworthEntropyProfile_tail_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)^3*∫ x,
      (entropyCentralSet n)ᶜ.indicator (uniformEdgeworthEntropyProfile n) x) atTop (𝓝 0) := by
  apply gaussian_scaled_tail_tendsto (uniformEdgeworthEntropyProfile)
    (fun x => entropyProfileTailPolynomial.eval (x^2)) 3 (1/2)
  · exact Filter.Eventually.of_forall fun n => (integrable_uniformEdgeworthEntropyProfile n).aestronglyMeasurable
  · exact entropyProfileTailPolynomial_nonneg
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    exact uniformEdgeworthEntropyProfile_gaussian_bound (by omega)
  · exact integrable_polynomial_gaussian (by norm_num : (0:ℝ)<1/2-3/7) entropyProfileTailPolynomial

end
end ENT.Quantitative
