module

public import ENT.Quantitative.EntropyExpansionAlgebra
public import ENT.Quantitative.EntropyExpansionGaussian

/-! Uniform Gaussian control of the central entropy approximation error.
One full inverse dimension is retained after absorbing all reference-density
 denominators on `exp(x²/7) ≤ n`. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory Polynomial Filter
open scoped Topology
namespace ENT.Quantitative
noncomputable section

def gaussianNormalizer : ℝ := Real.sqrt (2*Real.pi)

theorem gaussianNormalizer_pos : 0<gaussianNormalizer := by
  unfold gaussianNormalizer
  positivity

theorem standardGaussian_inverse_power (x : ℝ) (q : ℕ) :
    ((gaussianPDFReal 0 1 x)^q)⁻¹=
      gaussianNormalizer^q*Real.exp ((q:ℝ)*x^2/2) := by
  rw [standardGaussianPDF_eq,Pang.gaussianWeight,mul_pow,mul_inv_rev,inv_pow,inv_inv,
    ←Real.exp_natCast_mul,←Real.exp_neg]
  unfold gaussianNormalizer
  rw [mul_comm]
  congr 2
  ring

/-- The central cutoff pays for a negative power of the Gaussian PDF. -/
theorem central_gaussian_inverse_bound {n x : ℝ} (hn : 0<n)
    (hx : Real.exp (x^2/7)≤n) (k q : ℕ)
    (hgap : (q:ℝ)/2+(1/14:ℝ)≤(k:ℝ)/7) :
    1/(n^k*(gaussianPDFReal 0 1 x)^q)≤
      gaussianNormalizer^q*Real.exp (-(1/14:ℝ)*x^2) := by
  have hbase := one_div_le_one_div_of_le (Real.exp_pos (x^2/7)) hx
  simp only [one_div,←Real.exp_neg] at hbase
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hn.le) hbase k
  rw [inv_pow,←Real.exp_natCast_mul] at hp
  have hφ : 0<gaussianPDFReal 0 1 x := gaussianPDFReal_pos 0 1 x (by norm_num)
  calc
    _=(n^k)⁻¹*((gaussianPDFReal 0 1 x)^q)⁻¹ := by simp only [one_div,mul_inv_rev]; ring
    _≤Real.exp ((k:ℝ)*(-(x^2/7)))*((gaussianPDFReal 0 1 x)^q)⁻¹ :=
      mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr (pow_nonneg hφ.le q))
    _=gaussianNormalizer^q*Real.exp (((q:ℝ)/2-(k:ℝ)/7)*x^2) := by
      rw [standardGaussian_inverse_power,mul_left_comm,←Real.exp_add]
      congr 2
      ring
    _≤_ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg gaussianNormalizer_pos.le q)
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg x]

theorem standardGaussian_le_central_envelope (x : ℝ) :
    gaussianPDFReal 0 1 x≤gaussianNormalizer⁻¹*Real.exp (-(1/14:ℝ)*x^2) := by
  rw [standardGaussianPDF_eq]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr gaussianNormalizer_pos.le)
  unfold Pang.gaussianWeight
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg x]

def entropyCentralMajorant (M P : ℝ) : ℝ :=
  (8/3:ℝ)*gaussianNormalizer⁻¹*P^4+(8/3:ℝ)*M^4*gaussianNormalizer^3+
    P*M+M^2*gaussianNormalizer/2+P^2*M/2+P*M^2*gaussianNormalizer/2+
    M^3*gaussianNormalizer^2/6

theorem entropyCentralMajorant_nonneg {M P : ℝ} (hM : 0≤M) (hP : 0≤P) :
    0≤entropyCentralMajorant M P := by
  unfold entropyCentralMajorant
  have := gaussianNormalizer_pos
  positivity

/-- Quantitative central remainder, directly derived from the nonnegative
entropy Taylor error and the absolute density error. -/
theorem central_scaled_gibbsDefect_error {u d e P M n x : ℝ}
    (hu : 0≤u) (hn : 0<n) (hP : 0≤P) (hM : 0≤M)
    (hx : Real.exp (x^2/7)≤n)
    (he : u=gaussianPDFReal 0 1 x*(1+d)+e)
    (hd : |d|≤P/n) (herr : |e|≤M/n^4) :
    n^3*|gibbsDefect u (gaussianPDFReal 0 1 x)-
      gaussianPDFReal 0 1 x*(d^2/2-d^3/6)|≤
      entropyCentralMajorant M P*Real.exp (-(1/14:ℝ)*x^2)/n := by
  have hv : 0<gaussianPDFReal 0 1 x := gaussianPDFReal_pos 0 1 x (by norm_num)
  have h := scaled_gibbsDefect_profile_error hu hv hn hP hM he hd herr
  let v := gaussianPDFReal 0 1 x
  let g := gaussianNormalizer
  let E := Real.exp (-(1/14:ℝ)*x^2)
  have h0 := standardGaussian_le_central_envelope x
  have h1 := central_gaussian_inverse_bound hn hx 12 3 (by norm_num)
  have h2 := central_gaussian_inverse_bound hn hx 1 0 (by norm_num)
  have h3 := central_gaussian_inverse_bound hn hx 4 1 (by norm_num)
  have h4 := central_gaussian_inverse_bound hn hx 2 0 (by norm_num)
  have h5 := central_gaussian_inverse_bound hn hx 5 1 (by norm_num)
  have h6 := central_gaussian_inverse_bound hn hx 8 2 (by norm_num)
  norm_num only [pow_zero,mul_one,pow_one] at h2 h3 h4 h5
  have hb1 : (8/3:ℝ)*v*P^4≤(8/3:ℝ)*g⁻¹*P^4*E := by
    have hh := mul_le_mul_of_nonneg_right h0 (show (0:ℝ)≤(8/3)*P^4 by positivity)
    convert hh using 1 <;> ring
  have hb2 : (8/3:ℝ)*M^4/(n^12*v^3)≤(8/3:ℝ)*M^4*g^3*E := by
    have hh := mul_le_mul_of_nonneg_left h1 (show (0:ℝ)≤(8/3)*M^4 by positivity)
    convert hh using 1 <;> ring
  have hb3 : P*M/n≤P*M*E := by
    have hh := mul_le_mul_of_nonneg_left h2 (mul_nonneg hP hM)
    convert hh using 1 <;> ring
  have hb4 : M^2/(2*n^4*v)≤M^2*g/2*E := by
    have hh := mul_le_mul_of_nonneg_left h3 (show (0:ℝ)≤M^2/2 by positivity)
    convert hh using 1 <;> ring
  have hb5 : P^2*M/(2*n^2)≤P^2*M/2*E := by
    have hh := mul_le_mul_of_nonneg_left h4 (show (0:ℝ)≤P^2*M/2 by positivity)
    convert hh using 1 <;> ring
  have hb6 : P*M^2/(2*n^5*v)≤P*M^2*g/2*E := by
    have hh := mul_le_mul_of_nonneg_left h5 (show (0:ℝ)≤P*M^2/2 by positivity)
    convert hh using 1 <;> ring
  have hb7 : M^3/(6*n^8*v^2)≤M^3*g^2/6*E := by
    have hh := mul_le_mul_of_nonneg_left h6 (show (0:ℝ)≤M^3/6 by positivity)
    convert hh using 1 <;> ring
  have hb : (8/3:ℝ)*v*P^4+(8/3:ℝ)*M^4/(n^12*v^3)+P*M/n+
      M^2/(2*n^4*v)+P^2*M/(2*n^2)+P*M^2/(2*n^5*v)+M^3/(6*n^8*v^2)≤
      entropyCentralMajorant M P*E := by
    unfold entropyCentralMajorant
    dsimp [g] at *
    linarith
  apply h.trans
  have hh := div_le_div_of_nonneg_right hb hn.le
  dsimp [v,E] at hh
  convert hh using 1 <;> field_simp <;> ring

end
end ENT.Quantitative
