module

public import ENT.Quantitative.LargeCurvature
public import ENT.Quantitative.FourierLimits
public import ENT.Quantitative.FourierVanishing

/-! Uniform, asymptotically sharp lower curvature bounds. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

theorem tendsto_signedIntegralLower :
    Tendsto signedIntegralLower atTop (𝓝 (19/20:ℝ)) := by
  have h1 := (tendsto_const_div_dimension 6).mul_const (2/5:ℝ)
  have h2 := (tendsto_const_div_dimension 1).mul_const (70623/1000:ℝ)
  have h3 := (((tendsto_const_div_dimension 4).pow 3).mul_const (10395+12969:ℝ)).div_const 6
  have h := (((tendsto_const_nhds (x:=(19/20:ℝ))).sub h1).sub h2).sub h3
  convert h using 1
  · rfl
  · norm_num

theorem tendsto_firstSineLower :
    Tendsto firstSineLower atTop (𝓝 (1/2:ℝ)) := by
  have h := (tendsto_const_nhds (x:=(1/2:ℝ))).sub (tendsto_const_div_dimension (457/36))
  convert h using 1
  · funext n; unfold firstSineLower; ring
  · norm_num

theorem tendsto_parameterSignedLower (c : ℝ) :
    Tendsto (fun n => parameterSignedLower n c) atTop (𝓝 ((5-c)/2)) := by
  have h := tendsto_signedIntegralLower.add (tendsto_firstSineLower.const_mul (31/10-c))
  convert h using 1
  · rfl
  · congr 1; ring

theorem tendsto_parameterSignedRatio (c : ℝ) :
    Tendsto (fun n => parameterSignedLower n c/momentMajorant n 0) atTop (𝓝 ((5-c)/2)) := by
  have hm : Tendsto (fun n => momentMajorant n 0) atTop (𝓝 (1:ℝ)) := tendsto_momentMajorant 0
  simpa only [div_one, Pi.div_def] using (tendsto_parameterSignedLower c).div hm (by norm_num : (1:ℝ)≠0)

theorem signed_average_ratio_ge_of_parameter {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 256≤n) {c d : ℝ} (hc : c≤31/10) (hd : 0<d)
    (hparam : d ≤ parameterSignedLower n c/momentMajorant n 0) :
    d ≤ fourierAverage (fun u=>u*(u^2-c)*normalizedSumSin n t u)/fourierAverage (sumCos n t) := by
  have hm := momentMajorant_pos (by omega : 16≤n) 0 (by norm_num)
  have hA := fourierAverage_sumCos_le_majorant ht (by omega : 16≤n)
  have hA0 : 0<fourierAverage (sumCos n t) :=
    lt_trans (by norm_num) (quant_fourierAverage_sumCos_gt ht hn)
  have hp : 0≤parameterSignedLower n c := by
    have hmul := (le_div_iff₀ hm).mp hparam
    exact le_trans (mul_pos hd hm).le hmul
  calc
    d ≤ parameterSignedLower n c/momentMajorant n 0 := hparam
    _ ≤ parameterSignedLower n c/fourierAverage (sumCos n t) :=
      div_le_div_of_nonneg_left hp hA0 hA
    _ ≤ _ := div_le_div_of_nonneg_right (parameterSignedLower_le ht hn hc) hA0.le

/-- The second assertion of the manuscript's quantitative large-dimension proposition.
The dimension threshold is independent of the position and of the exponential tilt. -/
theorem large_curvature_eventually {ε : ℝ} (hε : 0<ε) (hεsmall : ε≤1/10) :
    ∃ N : ℕ, 256≤N ∧ ∀ n : ℕ, N≤n →
      ∀ x ∈ Ioo (0:ℝ) (Real.sqrt (n:ℝ)),
        (((54/5:ℝ)*(1-ε))/(n:ℝ))*x ≤
          deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x := by
  have hb : ∀ᶠ n : ℕ in atTop, derivativeBracketMajorant n < 3+ε :=
    tendsto_derivativeBracketMajorant.eventually (gt_mem_nhds (by linarith))
  have hr : ∀ᶠ n : ℕ in atTop, 1-ε < parameterSignedLower n (3+ε)/momentMajorant n 0 :=
    (tendsto_parameterSignedRatio (3+ε)).eventually (lt_mem_nhds (by linarith))
  have hevent : ∀ᶠ n : ℕ in atTop,
      256≤n ∧ derivativeBracketMajorant n<3+ε ∧
        1-ε<parameterSignedLower n (3+ε)/momentMajorant n 0 := by
    filter_upwards [eventually_ge_atTop 256, hb, hr] with n hn hb' hr'
    exact ⟨hn,hb',hr'⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  refine ⟨N,(hN N le_rfl).1,?_⟩
  intro n hn x hx
  have hn256 := (hN n hn).1
  obtain ⟨t,ht,_⟩ := existsUnique_tiltCenter (by omega : 0<n) hx
  have hbr := (standardizedDensity_lowerDerivativeBracket_le_majorant ht.1 hn256).trans
    (hN n hn).2.1.le
  have hd : 0<1-ε := by linarith
  have hratio := signed_average_ratio_ge_of_parameter ht.1 hn256
    (c:=3+ε) (d:=1-ε) (by linarith) hd (hN n hn).2.2.le
  have h := diagonalPotential_tilt_quantitative_lower ht.1 (by omega : 150≤n) hd hbr hratio
  rw [ht.2] at h
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h.le

/-- The same result in the dimensionless ratio formulation in the manuscript. -/
theorem large_curvature_ratio_eventually {ε : ℝ} (hε : 0<ε) (hεsmall : ε≤1/10) :
    ∃ N : ℕ, 256≤N ∧ ∀ n : ℕ, N≤n →
      ∀ x ∈ Ioo (0:ℝ) (Real.sqrt (n:ℝ)),
        (54/5:ℝ)*(1-ε) ≤
          (n:ℝ)*deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x/x := by
  obtain ⟨N,hN,h⟩ := large_curvature_eventually hε hεsmall
  refine ⟨N,hN,?_⟩
  intro n hn x hx
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hb := h n hn x hx
  apply (le_div_iff₀ hx.1).mpr
  have hmul := mul_le_mul_of_nonneg_left hb hnR.le
  have he : (n:ℝ)*(((54/5:ℝ)*(1-ε))/(n:ℝ)*x) = (54/5:ℝ)*(1-ε)*x := by
    field_simp
  rw [he] at hmul
  exact hmul

end
end ENT.Quantitative
