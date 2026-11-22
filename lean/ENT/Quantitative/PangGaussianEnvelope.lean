module

public import ENT.Quantitative.PangGaussianTail
public import ENT.Quantitative.EdgeworthDensityJets
public import ENT.Pang.FourierLogJet

/-! The actual standardized diagonal densities have a uniform Gaussian envelope
with exponent 4/9 in every sufficiently large dimension. -/

@[expose] public section
set_option autoImplicit false
open Set Filter ProbabilityTheory
open scoped Topology
namespace ENT.Quantitative
noncomputable section

theorem iteratedDeriv_scaledDensity_zero (f : ℝ→ℝ) (s : ℝ) (k : ℕ) :
    iteratedDeriv k (scaledDensity s f) 0=s⁻¹*(s⁻¹)^k*iteratedDeriv k f 0 := by
  have he : scaledDensity s f=(fun x=>s⁻¹*f (s⁻¹*x+0)) := by
    funext x
    unfold scaledDensity
    congr 1
    congr 1
    ring
  rw [he,iteratedDeriv_const_mul_field,Pang.iteratedDeriv_affine_comp]
  simp only [mul_zero,zero_add]
  ring

theorem diagonalPotential_second_zero_eq_ratio {n : ℕ} (hn : 5≤n) :
    deriv (deriv (Spline.diagonalSplinePotential n)) 0 =
      -3*iteratedDeriv 2 (standardizedDiagonalDensity n) 0/standardizedDiagonalDensity n 0 := by
  have hn0 : 0<n := by omega
  have hR : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn0)
  have hq0 := Spline.diagonalSplineDensity_pos n (by omega) 0 ⟨by linarith,hR⟩
  have hdiff : ContDiff ℝ 3 (Spline.diagonalSplineDensity n) :=
    Spline.contDiff_diagonalSplineDensity 3 n (by omega)
  have hd := hdiff.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (deriv (Spline.diagonalSplineDensity n)) :=
    (ContDiff.deriv' (n := 1) (hdiff.of_le (show (1:WithTop ℕ∞)+1≤3 by norm_num))).differentiable (by norm_num)
  have hlog : deriv (deriv (Spline.diagonalSplinePotential n)) 0 =
      -Pang.logSecondJet (Spline.diagonalSplineDensity n) 0 := by
    have hi : iteratedDeriv 2 (Spline.diagonalSplinePotential n) =
        deriv (deriv (Spline.diagonalSplinePotential n)) := by
      simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    rw [←hi]
    unfold Spline.diagonalSplinePotential
    rw [iteratedDeriv_fun_neg]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    rw [Pang.second_deriv_log_eq_logSecondJet hd hd1 hq0.ne']
  rw [hlog]
  unfold Pang.logSecondJet standardizedDiagonalDensity
  rw [Spline.deriv_diagonalSplineDensity_zero n (by omega),iteratedDeriv_scaledDensity_zero]
  simp only [scaledDensity,zero_div,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero]
  have hs : (0:ℝ)<Real.sqrt 3 := by positivity
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  field_simp [hq0.ne',hs.ne']
  norm_num [Real.sq_sqrt]

theorem diagonalPotential_second_zero_tendsto :
    Tendsto (fun n : ℕ=>deriv (deriv (Spline.diagonalSplinePotential n)) 0) atTop (𝓝 (3:ℝ)) := by
  have hp : 0<gaussianPDFReal 0 1 0 := gaussianPDFReal_pos 0 1 0 (by norm_num)
  have h := (standardizedDiagonalDensity_second_zero_tendsto.const_mul (-3)).div
    standardizedDiagonalDensity_zero_tendsto hp.ne'
  have hlim : (-3:ℝ)*(-gaussianPDFReal 0 1 0)/gaussianPDFReal 0 1 0=3 := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 5] with n hn
  exact (diagonalPotential_second_zero_eq_ratio hn).symm

/-- A dimension-independent Gaussian majorant for the genuine standardized PDF. -/
theorem standardizedDiagonalDensity_gaussian_envelope_eventually :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, 150≤N ∧ ∀ n : ℕ, N≤n → ∀ x : ℝ,
      standardizedDiagonalDensity n x≤C*Real.exp (-(4/9:ℝ)*x^2) := by
  let C : ℝ := gaussianPDFReal 0 1 0+1
  have hp : 0<gaussianPDFReal 0 1 0 := gaussianPDFReal_pos 0 1 0 (by norm_num)
  have hC : 0<C := by dsimp [C]; linarith
  have hjet : ∀ᶠ n : ℕ in atTop, (8/3:ℝ)≤deriv (deriv (Spline.diagonalSplinePotential n)) 0 :=
    (diagonalPotential_second_zero_tendsto.eventually (lt_mem_nhds (by norm_num : (8/3:ℝ)<3))).mono
      (fun _ hn=>hn.le)
  have hmass : ∀ᶠ n : ℕ in atTop, standardizedDiagonalDensity n 0≤C :=
    (standardizedDiagonalDensity_zero_tendsto.eventually (gt_mem_nhds (by dsimp [C]; linarith))).mono
      (fun _ hn=>hn.le)
  have he : ∀ᶠ n : ℕ in atTop, 150≤n ∧
      (8/3:ℝ)≤deriv (deriv (Spline.diagonalSplinePotential n)) 0 ∧
      standardizedDiagonalDensity n 0≤C := by
    filter_upwards [eventually_ge_atTop 150,hjet,hmass] with n hn hj hm
    exact ⟨hn,hj,hm⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨C,hC,N,(hN N le_rfl).1,?_⟩
  intro n hn x
  have henv := diagonal_density_gaussian_envelope (hN n hn).1 (hN n hn).2.1 (x/Real.sqrt 3)
  have hs : (0:ℝ)<Real.sqrt 3 := by positivity
  have hh := mul_le_mul_of_nonneg_left henv (inv_nonneg.mpr hs.le)
  have hexp : -(8/3:ℝ)*(x/Real.sqrt 3)^2/2=-(4/9:ℝ)*x^2 := by
    rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
    ring
  rw [hexp] at hh
  have hzero : (Real.sqrt 3)⁻¹*Spline.diagonalSplineDensity n 0=standardizedDiagonalDensity n 0 := by
    simp only [standardizedDiagonalDensity,scaledDensity,zero_div]
  calc
    standardizedDiagonalDensity n x≤standardizedDiagonalDensity n 0*Real.exp (-(4/9:ℝ)*x^2) := by
      simpa only [standardizedDiagonalDensity,scaledDensity,zero_div,mul_assoc] using hh
    _≤C*Real.exp (-(4/9:ℝ)*x^2) :=
      mul_le_mul_of_nonneg_right (hN n hn).2.2 (Real.exp_pos _).le

end
end ENT.Quantitative
