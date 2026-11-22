module

public import ENT.Pang.EnvelopePrimitive
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Envelope mass by the two-dimensional polar comparison

This proves the normalization estimate in Pang Appendix B without a Gamma
ratio estimate. The product inequality, polar substitution, and radial
improper integral all have checked measure-theoretic meanings.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

def envelopeMoment (n k : ℕ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * ∫ u : ℝ, u ^ (2 * k) * pangEnvelope n u

def complexEnvelope (n : ℕ) (z : ℂ) : ℝ :=
  (1 + ‖z‖ ^ 2 / (n : ℝ)) ^ (-((n : ℝ) - 1) / 2)

theorem integrable_complexEnvelope {n : ℕ} (hn : 3 < n) : Integrable (complexEnvelope n) := by
  have hnR : (3 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hb : Integrable (fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) - 1) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by rw [Complex.finrank_real_complex]; norm_num; linarith)
  have h := hb.comp_smul (R := (Real.sqrt (n : ℝ))⁻¹) (inv_ne_zero hs)
  convert h using 1
  funext z
  unfold complexEnvelope
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, inv_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ n)]
  congr 2
  ring

theorem product_envelope_le_complex {n : ℕ} (hn : 3 < n) (z : ℂ) :
    pangEnvelope n z.re * pangEnvelope n z.im ≤ complexEnvelope n z := by
  have hnR : (3 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 ≤ z.re ^ 2 / (n : ℝ) := by positivity
  have hy : 0 ≤ z.im ^ 2 / (n : ℝ) := by positivity
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hbase : 1 + ‖z‖ ^ 2 / (n : ℝ) ≤
      (1 + z.re ^ 2 / (n : ℝ)) * (1 + z.im ^ 2 / (n : ℝ)) := by
    rw [hnorm, add_div]
    nlinarith [mul_nonneg hx hy]
  unfold pangEnvelope complexEnvelope
  rw [← Real.mul_rpow (by positivity : 0 ≤ 1 + z.re ^ 2 / (n : ℝ))
    (by positivity : 0 ≤ 1 + z.im ^ 2 / (n : ℝ))]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)

theorem integral_complexEnvelope {n : ℕ} (hn : 3 < n) :
    (∫ z : ℂ, complexEnvelope n z) = 2 * Real.pi * (n : ℝ) / ((n : ℝ) - 3) := by
  calc
    (∫ z : ℂ, complexEnvelope n z) =
        ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 * pangEnvelope n p.1 := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      simp only [complexEnvelope, Complex.norm_polarCoord_symm, sq_abs,
        smul_eq_mul, pangEnvelope]
    _ = (∫ r in Ioi (0 : ℝ), r * pangEnvelope n r) *
        ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← setIntegral_prod_mul, Measure.volume_eq_prod]
      simp only [mul_one]
    _ = 2 * Real.pi * (n : ℝ) / ((n : ℝ) - 3) := by
      rw [integral_radial_envelope hn]
      simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ,
        Set.univ_inter, smul_eq_mul, mul_one]
      rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
      ring

theorem integral_envelope_sq_le {n : ℕ} (hn : 3 < n) :
    (∫ u : ℝ, pangEnvelope n u) ^ 2 ≤ 2 * Real.pi * (n : ℝ) / ((n : ℝ) - 3) := by
  have hi : Integrable (pangEnvelope n) := by
    simpa only [pow_zero, one_mul] using
      integrable_abs_pow_mul_pangEnvelope (n := n) (k := 0) (by omega)
  have hip : Integrable (fun p : ℝ × ℝ => pangEnvelope n p.1 * pangEnvelope n p.2) :=
    hi.mul_prod hi
  have hic : Integrable (fun z : ℂ => pangEnvelope n z.re * pangEnvelope n z.im) :=
    Complex.volume_preserving_equiv_real_prod.integrable_comp_of_integrable hip
  calc
    (∫ u : ℝ, pangEnvelope n u) ^ 2 =
        ∫ p : ℝ × ℝ, pangEnvelope n p.1 * pangEnvelope n p.2 := by
      rw [pow_two, ← integral_prod_mul]
      rfl
    _ = ∫ z : ℂ, pangEnvelope n z.re * pangEnvelope n z.im :=
      (Complex.volume_preserving_equiv_real_prod.integral_comp
        Complex.measurableEquivRealProd.measurableEmbedding _).symm
    _ ≤ ∫ z : ℂ, complexEnvelope n z :=
      integral_mono hic (integrable_complexEnvelope hn) (product_envelope_le_complex hn)
    _ = _ := integral_complexEnvelope hn

theorem envelopeMoment_nonneg {n : ℕ} (hn : 0 < n) (k : ℕ) :
    0 ≤ envelopeMoment n k := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro u
  have hp : 0 ≤ u ^ (2 * k) := by rw [pow_mul]; positivity
  exact mul_nonneg hp (pangEnvelope_pos hn u).le

theorem envelopeMoment_zero_sq_le {n : ℕ} (hn : 3 < n) :
    envelopeMoment n 0 ^ 2 ≤ (n : ℝ) / ((n : ℝ) - 3) := by
  have h := integral_envelope_sq_le hn
  have hpi : 0 < 2 * Real.pi := by positivity
  have he : envelopeMoment n 0 ^ 2 = (∫ u : ℝ, pangEnvelope n u) ^ 2 / (2 * Real.pi) := by
    simp only [envelopeMoment, mul_zero, pow_zero, one_mul, mul_pow, div_pow, one_pow,
      Real.sq_sqrt hpi.le]
    ring
  rw [he]
  apply (div_le_iff₀ hpi).mpr
  convert h using 1 <;> ring

/-- Pang's elementary bound (67), with a non-strict endpoint. -/
theorem envelopeMoment_zero_le {n : ℕ} (hn : 3 < n) :
    envelopeMoment n 0 ≤ (2 * (n : ℝ) - 3) / (2 * ((n : ℝ) - 3)) := by
  have hnR : (3 : ℝ) < n := by exact_mod_cast hn
  have hn3 : (n : ℝ) - 3 ≠ 0 := by linarith
  have hm := envelopeMoment_zero_sq_le hn
  have hm0 := envelopeMoment_nonneg (by omega : 0 < n) 0
  have hq : 0 ≤ (2 * (n : ℝ) - 3) / (2 * ((n : ℝ) - 3)) :=
    div_nonneg (by linarith) (mul_nonneg (by norm_num) (by linarith))
  have he : ((2 * (n : ℝ) - 3) / (2 * ((n : ℝ) - 3))) ^ 2 -
      (n : ℝ) / ((n : ℝ) - 3) = 9 / (4 * ((n : ℝ) - 3) ^ 2) := by
    field_simp [hn3]
    ring
  have hp : 0 ≤ 9 / (4 * ((n : ℝ) - 3) ^ 2) := by positivity
  nlinarith

end
end ENT.Pang
