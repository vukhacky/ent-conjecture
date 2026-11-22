module

public import ENT.Quantitative.EntropyExpansionCentralGaussian
public import ENT.Quantitative.FourierLimits

/-! Integrability of the central majorant and a dominated-convergence lemma
for errors bounded by a fixed integrable function divided by the dimension. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory Polynomial Filter
open scoped Topology
namespace ENT.Quantitative
noncomputable section

def entropyCentralMajorantPolynomial (M : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C ((8/3:ℝ)*gaussianNormalizer⁻¹)*p^4+C ((8/3:ℝ)*M^4*gaussianNormalizer^3)+
    C M*p+C (M^2*gaussianNormalizer/2)+C (M/2)*p^2+
    C (M^2*gaussianNormalizer/2)*p+C (M^3*gaussianNormalizer^2/6)

theorem entropyCentralMajorantPolynomial_eval (M y : ℝ) (p : ℝ[X]) :
    (entropyCentralMajorantPolynomial M p).eval y=entropyCentralMajorant M (p.eval y) := by
  simp only [entropyCentralMajorantPolynomial,entropyCentralMajorant,eval_add,eval_mul,eval_pow,eval_C]
  ring

theorem integrable_entropyCentralMajorant (M : ℝ) (p : ℝ[X]) :
    Integrable (fun x : ℝ=>entropyCentralMajorant M (p.eval (x^2))*Real.exp (-(1/14:ℝ)*x^2)) := by
  simpa only [entropyCentralMajorantPolynomial_eval] using
    integrable_polynomial_gaussian (by norm_num : (0:ℝ)<1/14) (entropyCentralMajorantPolynomial M p)

/-- DCT with a fixed integrable majorant and an explicit inverse-dimension
rate; no measurability or integrability assumptions are silently dropped. -/
theorem integral_tendsto_zero_of_div_dimension (F : ℕ→ℝ→ℝ) (B : ℝ→ℝ)
    (hmeas : ∀ᶠn : ℕ in atTop,AEStronglyMeasurable (F n) volume)
    (hB : ∀x,0≤B x) (hBi : Integrable B)
    (hbound : ∀ᶠn : ℕ in atTop,∀x, ‖F n x‖≤B x/(n:ℝ)) :
    Tendsto (fun n : ℕ=>∫x,F n x) atTop (𝓝 0) := by
  have hb : ∀ᶠn : ℕ in atTop,∀ᵐx : ℝ, ‖F n x‖≤B x := by
    filter_upwards [hbound,eventually_ge_atTop (1:ℕ)] with n hn hn1
    exact Filter.Eventually.of_forall fun x=>(hn x).trans <|
      (div_le_self (hB x) (by exact_mod_cast hn1))
  have hl : ∀ᵐx : ℝ,Tendsto (fun n : ℕ=>F n x) atTop (𝓝 (0:ℝ)) :=
    Filter.Eventually.of_forall fun x=>by
      apply squeeze_zero_norm' (hbound.mono (fun n hn=>hn x))
      exact tendsto_const_div_dimension (B x)
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence B hmeas hb hBi hl

end
end ENT.Quantitative
