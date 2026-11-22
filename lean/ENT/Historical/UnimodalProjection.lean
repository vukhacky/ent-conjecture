module

public import ENT.Historical.Unimodal
public import ENT.IIDAE

/-! Every finite continuous-uniform residual law is either the Dirac mass at
zero or has a bounded, compactly supported, even unimodal finite-entropy
density. Signed coefficients and arbitrary patterns of zero coefficients are
included. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ENT.Comparison
noncomputable section

def HasEvenUnimodalDensity (μ : Measure ℝ) : Prop :=
  ∃ p : FiniteEntropyDensity μ, ∃ M R : ℝ,
    (∀ x, p.density x ≤ M) ∧
    (∀ x, x ∉ Icc (-R) R → p.density x = 0) ∧
    IsEvenUnimodal p.density

theorem convolutionDensity_uniform_eq_average {g : ℝ → ℝ}
    (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x) {M : ℝ} (hM : ∀ x, g x ≤ M)
    (c x : ℝ) :
    convolutionDensity (uniformUnit.map (fun u => c*u)) g x = uniformAverage c g x := by
  have hi : Integrable (fun y => g (x-y)) (uniformUnit.map (fun u => c*u)) := by
    apply Integrable.of_bound (hg.comp (by fun_prop)).aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun y => by
      simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (h0 _)] using hM (x-y)
  have he := integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun y => h0 (x-y))) hi.aestronglyMeasurable
  change (∫⁻ y, ENNReal.ofReal (g (x-y)) ∂uniformUnit.map (fun u => c*u)).toReal = _
  rw [← he, integral_map (f := fun y : ℝ => g (x-y)) (measurable_const_mul c).aemeasurable
    (hg.comp (by fun_prop)).aestronglyMeasurable]
  have hsign := integral_map (μ := uniformUnit) measurable_neg.aemeasurable
    (f := fun u => g (x-c*u)) (hg.comp (by fun_prop)).aestronglyMeasurable
  rw [uniformUnit_map_neg] at hsign
  rw [hsign]
  unfold uniformAverage
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    change g (x-c*(-u)) = g (x+c*u)
    congr 1
    ring

theorem scaled_uniform_ae_mem {c : ℝ} (hc : 0 ≤ c) :
    ∀ᵐ y ∂uniformUnit.map (fun u => c*u), y ∈ Icc (-c) c := by
  apply (ae_map_iff (measurable_const_mul c).aemeasurable measurableSet_Icc).mpr
  filter_upwards [uniformUnit_ae_mem] with u hu
  have hlo := mul_le_mul_of_nonneg_left hu.1 hc
  have hhi := mul_le_mul_of_nonneg_left hu.2 hc
  exact ⟨by simpa only [mul_neg,mul_one] using hlo, by simpa only [mul_one] using hhi⟩

theorem HasEvenUnimodalDensity.conv_uniform {μ : Measure ℝ}
    (h : HasEvenUnimodalDensity μ) {c : ℝ} (hc : 0 ≤ c) :
    HasEvenUnimodalDensity (Measure.conv μ (uniformUnit.map (fun u => c*u))) := by
  obtain ⟨p,M,R,hM,hR,hU⟩ := h
  let ν := uniformUnit.map (fun u => c*u)
  let q := convolutionFiniteEntropyDensity p ν M R c hM hR (scaled_uniform_ae_mem hc)
  have hq : q.density = convolutionDensity ν p.density := rfl
  refine ⟨q,M,R+c,?_,?_,?_⟩
  · rw [hq]
    exact convolutionDensity_le ν ((p.nonneg 0).trans (hM 0)) hM
  · rw [hq]
    exact convolutionDensity_eq_zero_of_not_mem ν hR (scaled_uniform_ae_mem hc)
  · have heq : q.density = uniformAverage c p.density := by
      rw [hq]
      funext x
      exact convolutionDensity_uniform_eq_average p.measurable p.nonneg hM c x
    rw [heq]
    exact hU.uniformAverage p.measurable p.integrable hc

theorem projectionLaw_eq_dirac_of_zero {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, a i = 0) : projectionLaw a = Measure.dirac 0 := by
  have heq : projection a = fun _ => 0 := by
    funext x
    simp only [projection, ha, zero_mul, Finset.sum_const_zero]
  simp only [projectionLaw, heq, Measure.map_const, measure_univ, one_smul]

theorem projectionLaw_even_unimodal_or_zero_nonneg {n : ℕ}
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∀ i, a i = 0) ∨ HasEvenUnimodalDensity (projectionLaw a) := by
  induction n with
  | zero => exact Or.inl fun i => Fin.elim0 i
  | succ n ih =>
      let r := removeCoefficient a 0
      have hr : ∀ i, 0 ≤ r i := fun i => ha _
      rcases ih r hr with hr0 | hrU
      · by_cases hc0 : a 0 = 0
        · left
          intro i
          refine Fin.cases hc0 (fun j => ?_) i
          simpa only [r,removeCoefficient,Fin.succAbove_zero] using hr0 j
        · right
          have hcp : 0 < a 0 := lt_of_le_of_ne (ha 0) (Ne.symm hc0)
          have hlaw : projectionLaw a = uniformUnit.map (fun u => a 0*u) := by
            rw [projectionLaw_eq_conv_remove a 0, projectionLaw_eq_dirac_of_zero r hr0]
            simp
          rw [hlaw]
          refine ⟨scaledUniformFiniteEntropyDensity (a 0) hcp,(2*a 0)⁻¹,a 0,?_,?_,?_⟩
          · exact scaledUniformDensity_le hcp
          · exact scaledUniformDensity_eq_zero_of_not_mem (a 0)
          · exact scaledUniformDensity_even_unimodal hcp
      · right
        have hconv := hrU.conv_uniform (ha 0)
        have hlaw : projectionLaw a =
            Measure.conv (projectionLaw r) (uniformUnit.map (fun u => a 0*u)) := by
          rw [projectionLaw_eq_conv_remove a 0]
          exact Measure.conv_comm _ _
        rwa [← hlaw] at hconv

/-- Signed and zero coefficients are admitted. The all-zero vector is the
only branch where no Lebesgue density is asserted. -/
theorem projectionLaw_even_unimodal_or_zero {n : ℕ} (a : Fin n → ℝ) :
    (∀ i, a i = 0) ∨ HasEvenUnimodalDensity (projectionLaw a) := by
  rcases projectionLaw_even_unimodal_or_zero_nonneg (fun i => |a i|)
    (fun i => abs_nonneg (a i)) with hz | hU
  · exact Or.inl fun i => abs_eq_zero.mp (hz i)
  · exact Or.inr (by simpa only [projectionLaw_abs] using hU)

theorem projectionLaw_residual_dichotomy {n : ℕ} (a : Fin n → ℝ) :
    projectionLaw a = Measure.dirac 0 ∨ HasEvenUnimodalDensity (projectionLaw a) := by
  rcases projectionLaw_even_unimodal_or_zero a with hz | hU
  · exact Or.inl (projectionLaw_eq_dirac_of_zero a hz)
  · exact Or.inr hU

universe u

theorem iid_residual_dichotomy_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformUnit)
    (a : Fin n → ℝ) :
    μ.map (fun ω => ∑ i, a i*U i ω) = Measure.dirac 0 ∨
      HasEvenUnimodalDensity (μ.map (fun ω => ∑ i, a i*U i ω)) := by
  rw [weightedLaw_eq_projectionLaw_ae μ U hU hind hlaw a]
  exact projectionLaw_residual_dichotomy a

end
end ENT.Comparison
