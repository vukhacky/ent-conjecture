module

public import ENT.Quantitative.EntropyExpansionDomination
public import ENT.Quantitative.EdgeworthEntropyProfile

/-! Application of the central entropy remainder to the actual standardized
uniform densities. The only input is the separately stated absolute density
expansion, together with an explicit polynomial majorant for its profile. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory Polynomial Filter
open scoped Topology
namespace ENT.Quantitative
noncomputable section

theorem standardizedDiagonal_gibbs_central_error_tendsto
    (hE : UniformDensityEdgeworthBound) (P : ℝ[X])
    (hP : ∀x : ℝ,0≤P.eval (x^2))
    (hprofile : ∀n : ℕ,0<n→∀x : ℝ,
      |uniformEdgeworthRelativeProfile n x|≤P.eval (x^2)/(n:ℝ)) :
    Tendsto (fun n : ℕ=>(n:ℝ)^3*∫x, (entropyCentralSet n).indicator
      (fun x=>gibbsDefect (standardizedDiagonalDensity n x) (gaussianPDFReal 0 1 x)-
        uniformEdgeworthEntropyProfile n x) x) atTop (𝓝 0) := by
  obtain ⟨M,hM,N,hN,happrox⟩ := hE
  let B : ℝ→ℝ := fun x=>entropyCentralMajorant M (P.eval (x^2))*Real.exp (-(1/14:ℝ)*x^2)
  have hB (x : ℝ) : 0≤B x :=
    mul_nonneg (entropyCentralMajorant_nonneg hM.le (hP x)) (Real.exp_pos _).le
  have hBi : Integrable B := integrable_entropyCentralMajorant M P
  let F : ℕ→ℝ→ℝ := fun n=>(entropyCentralSet n).indicator (fun x=>(n:ℝ)^3*
    (gibbsDefect (standardizedDiagonalDensity n x) (gaussianPDFReal 0 1 x)-
      uniformEdgeworthEntropyProfile n x))
  have hm : ∀ᶠn : ℕ in atTop,AEStronglyMeasurable (F n) volume := by
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    exact (((integrable_standardizedDiagonal_gibbs hn).sub
      (integrable_uniformEdgeworthEntropyProfile n)).const_mul _).aestronglyMeasurable.indicator
        (measurableSet_entropyCentralSet n)
  have hb : ∀ᶠn : ℕ in atTop,∀x, ‖F n x‖≤B x/(n:ℝ) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn0 : 0<n := by omega
    have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn0
    intro x
    by_cases hx : x∈entropyCentralSet n
    · simp only [F,indicator_of_mem hx,Real.norm_eq_abs,abs_mul,
        abs_of_nonneg (show (0:ℝ)≤(n:ℝ)^3 by positivity)]
      let e := standardizedDiagonalDensity n x-uniformEdgeworthApprox n x
      have he : standardizedDiagonalDensity n x=gaussianPDFReal 0 1 x*
          (1+uniformEdgeworthRelativeProfile n x)+e := by
        dsimp [e]
        rw [uniformEdgeworthApprox_eq_relative]
        ring
      exact central_scaled_gibbsDefect_error
        ((standardizedDiagonalFiniteEntropyDensity n (by omega)).nonneg x)
        hnR (hP x) hM.le hx he (hprofile n hn0 x) (happrox n hn x)
    · simp only [F,indicator_of_notMem hx,norm_zero]
      exact div_nonneg (hB x) hnR.le
  have ht := integral_tendsto_zero_of_div_dimension F B hm hB hBi hb
  apply ht.congr'
  exact Filter.Eventually.of_forall fun n=>by
    dsimp only
    rw [←integral_const_mul]
    congr 1
    funext x
    by_cases hx : x∈entropyCentralSet n <;> simp [F,hx]

/-- Decomposition with integrability established before any Bochner integral
linearity is used. -/
theorem integral_difference_central_tail {f g : ℝ→ℝ} (hf : Integrable f) (hg : Integrable g)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (∫x,f x)-(∫x,g x)=(∫x,S.indicator (fun x=>f x-g x) x)+
      (∫x,Sᶜ.indicator f x)-(∫x,Sᶜ.indicator g x) := by
  have hfi := integral_add_compl hS hf
  have hgi := integral_add_compl hS hg
  rw [←integral_indicator hS,←integral_indicator hS.compl] at hfi hgi
  have hsub : (∫x,S.indicator (fun x=>f x-g x) x)=
      (∫x,S.indicator f x)-(∫x,S.indicator g x) := by
    have he : S.indicator (fun x=>f x-g x)=(fun x=>S.indicator f x-S.indicator g x) := by
      funext x
      by_cases hx : x∈S <;> simp [hx]
    rw [he,integral_sub (hf.indicator hS) (hg.indicator hS)]
  rw [hsub]
  linarith

end
end ENT.Quantitative
