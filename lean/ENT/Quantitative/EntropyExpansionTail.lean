module

public import ENT.Quantitative.EntropyExpansionGaussian

/-! Vanishing entropy tails on the complement of `x² ≤ 7 log n`.
All estimates concern the genuine integrands and include measurability. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory Polynomial Filter
open scoped Topology
namespace ENT.Quantitative
noncomputable section

/-- An envelope criterion for scaled integrals over the expanding Gaussian tail. -/
theorem gaussian_scaled_tail_tendsto (F : ℕ→ℝ→ℝ) (P : ℝ→ℝ) (k : ℕ) (b : ℝ)
    (hmeas : ∀ᶠn : ℕ in atTop, AEStronglyMeasurable (F n) volume)
    (hP : ∀x,0≤P x)
    (hbound : ∀ᶠn : ℕ in atTop, ∀x, |F n x|≤P x*Real.exp (-b*x^2))
    (hint : Integrable (fun x=>P x*Real.exp (-(b-(k:ℝ)/7)*x^2))) :
    Tendsto (fun n : ℕ=>(n:ℝ)^k*∫x, (entropyCentralSet n)ᶜ.indicator (F n) x)
      atTop (𝓝 0) := by
  let H : ℕ→ℝ→ℝ := fun n=>(entropyCentralSet n)ᶜ.indicator (fun x=>(n:ℝ)^k*F n x)
  have hm : ∀ᶠn : ℕ in atTop,AEStronglyMeasurable (H n) volume := by
    filter_upwards [hmeas] with n hn
    exact (hn.const_mul _).indicator (measurableSet_entropyCentralSet n).compl
  have hb : ∀ᶠn : ℕ in atTop,∀ᵐx : ℝ, ‖H n x‖≤P x*Real.exp (-(b-(k:ℝ)/7)*x^2) := by
    filter_upwards [hbound] with n hn
    exact Filter.Eventually.of_forall fun x=>by
      by_cases hx : x∈entropyCentralSet n
      · simp only [H,indicator_of_notMem (show x∉(entropyCentralSet n)ᶜ from fun h=>h hx),norm_zero]
        exact mul_nonneg (hP x) (Real.exp_pos _).le
      · have hnexp : (n:ℝ)≤Real.exp (x^2/7) := (lt_of_not_ge hx).le
        have hpow := pow_le_pow_left₀ (Nat.cast_nonneg n) hnexp k
        rw [←Real.exp_natCast_mul] at hpow
        simp only [H,indicator_of_mem (show x∈(entropyCentralSet n)ᶜ from hx),
          Real.norm_eq_abs,abs_mul,abs_of_nonneg (show (0:ℝ)≤(n:ℝ)^k by positivity)]
        calc
          (n:ℝ)^k*|F n x|≤Real.exp ((k:ℝ)*(x^2/7))*(P x*Real.exp (-b*x^2)) :=
            mul_le_mul hpow (hn x) (abs_nonneg _) (Real.exp_pos _).le
          _=P x*Real.exp (-(b-(k:ℝ)/7)*x^2) := by
            rw [mul_left_comm,←Real.exp_add]
            congr 2
            ring
  have hl : ∀ᵐx : ℝ,Tendsto (fun n : ℕ=>H n x) atTop (𝓝 (0:ℝ)) :=
    Filter.Eventually.of_forall fun x=>tendsto_const_nhds.congr' <| by
      filter_upwards [eventually_mem_entropyCentralSet x] with n hn
      simp only [H,indicator_of_notMem (show x∉(entropyCentralSet n)ᶜ from fun h=>h hn)]
  have ht := tendsto_integral_filter_of_dominated_convergence _ hm hb hint hl
  simp only [integral_zero] at ht
  apply ht.congr'
  exact Filter.Eventually.of_forall fun n=>by
    dsimp only
    rw [←integral_const_mul]
    congr 1
    funext x
    by_cases hx : x∈entropyCentralSet n <;> simp [H,hx]

/-- The actual standardized uniform densities have entropy tails `o(n⁻³)`. -/
theorem standardizedDiagonal_gibbs_tail_tendsto :
    Tendsto (fun n : ℕ=>(n:ℝ)^3*∫x,
      (entropyCentralSet n)ᶜ.indicator
        (fun x=>gibbsDefect (standardizedDiagonalDensity n x) (gaussianPDFReal 0 1 x)) x)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,N,hN,henv⟩ := standardizedDiagonalDensity_gaussian_envelope_eventually
  let K : ℝ := gibbsGaussianConstant C
  have hK : 0<K := gibbsGaussianConstant_pos hC
  have hboundK : ∀ᶠn : ℕ in atTop, ∀x,
      |gibbsDefect (standardizedDiagonalDensity n x) (gaussianPDFReal 0 1 x)|≤
        K*(1+x^2)*Real.exp (-(7/16:ℝ)*x^2) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact gibbsDefect_gaussian_envelope_bound hC
      ((standardizedDiagonalFiniteEntropyDensity n (by omega)).nonneg) (henv n hn)
  apply gaussian_scaled_tail_tendsto _ (fun x=>K*(1+x^2)) 3 (7/16)
  · filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    have hm := (standardizedDiagonalFiniteEntropyDensity n hn).measurable
    unfold gibbsDefect
    exact ((((Real.continuous_mul_log.measurable.comp hm).sub
      (hm.mul (Real.measurable_log.comp (measurable_gaussianPDFReal 0 1)))).sub hm).add
      (measurable_gaussianPDFReal 0 1)).aestronglyMeasurable
  · intro x
    positivity
  · exact hboundK
  · have hi := (integrable_polynomial_gaussian (by norm_num : (0:ℝ)<7/16-3/7)
      (Polynomial.C 1+X)).const_mul K
    simpa only [eval_add,eval_C,eval_X,mul_assoc,Nat.cast_ofNat] using hi

end
end ENT.Quantitative
