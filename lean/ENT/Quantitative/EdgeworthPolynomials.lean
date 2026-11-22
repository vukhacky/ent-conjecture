module

public import ENT.Quantitative.EdgeworthHermite
public import ENT.Quantitative.EdgeworthCharacteristic

/-! Polynomial correction terms and their moments in the density expansion for standardized uniform sums. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Polynomial

namespace ENT.Quantitative
noncomputable section

def hermite10Even : ℝ[X] := X^5 - C 45*X^4 + C 630*X^3 - C 3150*X^2 + C 4725*X - C 945

def hermite12Even : ℝ[X] := X^6 - C 66*X^5 + C 1485*X^4 - C 13860*X^3 +
  C 51975*X^2 - C 62370*X + C 10395

def uniformEdgeworthC : ℝ[X] :=
  C (-3/1400)*hermite8Even + C (-1/2100)*hermite10Even + C (-1/48000)*hermite12Even

def uniformEdgeworthApprox (n : ℕ) (x : ℝ) : ℝ :=
  gaussianPDFReal 0 1 x * (1 + uniformEdgeworthA.eval (x^2)/(n:ℝ) +
    uniformEdgeworthB.eval (x^2)/(n:ℝ)^2 + uniformEdgeworthC.eval (x^2)/(n:ℝ)^3)

/-- The intended absolute uniform density error after the three correction
profiles. This declaration is a proposition, not a claimed theorem. -/
def UniformDensityEdgeworthBound : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ x : ℝ,
    |standardizedDiagonalDensity n x-uniformEdgeworthApprox n x| ≤ M/(n:ℝ)^4

theorem gaussianEvenPolynomialIntegral_X_pow (k : ℕ) :
    gaussianEvenPolynomialIntegral (X^k) = Pang.gaussianCap k := by
  simpa only [map_one, one_mul] using gaussianEvenPolynomialIntegral_C_mul_X_pow 1 k

theorem gaussianIntegral_hermite6 : gaussianEvenPolynomialIntegral hermite6Even = 0 := by
  unfold hermite6Even
  simp only [map_add, map_sub, gaussianEvenPolynomialIntegral_X_pow,
    show C (45:ℝ)*X = C 45*X^1 by simp,
    gaussianEvenPolynomialIntegral_C_mul_X_pow, gaussianEvenPolynomialIntegral_C]
  norm_num [Pang.gaussianCap]

theorem gaussianIntegral_hermite8 : gaussianEvenPolynomialIntegral hermite8Even = 0 := by
  unfold hermite8Even
  simp only [map_add, map_sub, gaussianEvenPolynomialIntegral_X_pow,
    show C (420:ℝ)*X = C 420*X^1 by simp,
    gaussianEvenPolynomialIntegral_C_mul_X_pow, gaussianEvenPolynomialIntegral_C]
  norm_num [Pang.gaussianCap]

theorem gaussianIntegral_hermite10 : gaussianEvenPolynomialIntegral hermite10Even = 0 := by
  unfold hermite10Even
  simp only [map_add, map_sub, gaussianEvenPolynomialIntegral_X_pow,
    show C (4725:ℝ)*X = C 4725*X^1 by simp,
    gaussianEvenPolynomialIntegral_C_mul_X_pow, gaussianEvenPolynomialIntegral_C]
  norm_num [Pang.gaussianCap]

theorem gaussianIntegral_hermite12 : gaussianEvenPolynomialIntegral hermite12Even = 0 := by
  unfold hermite12Even
  simp only [map_add, map_sub, gaussianEvenPolynomialIntegral_X_pow,
    show C (62370:ℝ)*X = C 62370*X^1 by simp,
    gaussianEvenPolynomialIntegral_C_mul_X_pow, gaussianEvenPolynomialIntegral_C]
  norm_num [Pang.gaussianCap]

theorem gaussianIntegral_uniformEdgeworthA : gaussianEvenPolynomialIntegral uniformEdgeworthA = 0 := by
  have he : uniformEdgeworthA = (-1/20:ℝ) • hermite4Even := by
    simp only [uniformEdgeworthA, smul_eq_C_mul]
  rw [he, map_smul, gaussianIntegral_hermite4, smul_zero]

theorem gaussianIntegral_uniformEdgeworthB : gaussianEvenPolynomialIntegral uniformEdgeworthB = 0 := by
  have he : uniformEdgeworthB = (1/105:ℝ) • hermite6Even + (1/800:ℝ) • hermite8Even := by
    simp only [uniformEdgeworthB, smul_eq_C_mul]
  rw [he, map_add, map_smul, map_smul, gaussianIntegral_hermite6, gaussianIntegral_hermite8]
  simp

theorem gaussianIntegral_uniformEdgeworthC : gaussianEvenPolynomialIntegral uniformEdgeworthC = 0 := by
  have he : uniformEdgeworthC = (-3/1400:ℝ) • hermite8Even +
      (-1/2100:ℝ) • hermite10Even + (-1/48000:ℝ) • hermite12Even := by
    simp only [uniformEdgeworthC, smul_eq_C_mul]
  rw [he, map_add, map_add, map_smul, map_smul, map_smul,
    gaussianIntegral_hermite8, gaussianIntegral_hermite10, gaussianIntegral_hermite12]
  simp

end
end ENT.Quantitative
