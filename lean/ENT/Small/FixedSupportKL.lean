module

public import ENT.Small.LocalGeometry
public import ENT.Small.EndpointLog
public import ENT.Basic.ProjectionDensityBounds
public import ENT.Entropy.Scaling
public import ENT.Comparison.KLInterior

/-! The fixed-support variational inequality with all density, endpoint,
cross-integrability and scaling hypotheses discharged for positive coefficients. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators

namespace ENT.Small

noncomputable section

def closedSupportFiniteKLData {μ : Measure ℝ} {n : ℕ} (hn : 2 ≤ n)
    (p : FiniteEntropyDensity μ) {M : ℝ} (hM : ∀ᵐ x ∂volume, p.density x ≤ M)
    (hsupport : ∀ᵐ x ∂μ, x ∈ Icc (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    FiniteKLData p (Spline.diagonalFiniteEntropyDensity n hn) where
  cross_integrable := by
    exact (integrable_log_diagonalSplineDensity n hn).bdd_mul p.measurable.aestronglyMeasurable
      (hM.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg (p.nonneg x)] using hx)
  support_ae := by
    have hleft : ∀ᵐ x : ℝ ∂volume, x ≠ -Real.sqrt (n : ℝ) := by simp [ae_iff]
    have hright : ∀ᵐ x : ℝ ∂volume, x ≠ Real.sqrt (n : ℝ) := by simp [ae_iff]
    filter_upwards [p.ae_nonzero_imp hsupport, hleft, hright] with x hx hxl hxr
    intro hq
    by_contra hp
    have hxmem := hx hp
    have hpos := Spline.diagonalSplineDensity_pos n hn x
      ⟨lt_of_le_of_ne hxmem.1 (Ne.symm hxl), lt_of_le_of_ne hxmem.2 hxr⟩
    exact hpos.ne' hq

/-- Finite cross entropy holds for every unit projection, including a diagonal
projection whose support reaches both logarithmic endpoints. -/
def unitProjectionFiniteKLData {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℝ) (ha : IsUnit a) (p : FiniteEntropyDensity (projectionLaw a)) :
    FiniteKLData p (Spline.diagonalFiniteEntropyDensity n hn) := by
  obtain ⟨M, hM⟩ := projection_density_exists_ae_bound a ha p
  apply closedSupportFiniteKLData hn p hM
  have hR := projectionRadius_le_sqrt a ha
  filter_upwards [projectionLaw_ae_mem a] with x hx
  exact ⟨le_trans (neg_le_neg hR) hx.1, le_trans hx.2 hR⟩

theorem integral_self_potential_eq_entropy {μ : Measure ℝ} (p : FiniteEntropyDensity μ) :
    (∫ x, -Real.log (p.density x) ∂μ) = p.entropy := by
  rw [p.integral_eq_density]
  unfold FiniteEntropyDensity.entropy
  rw [← integral_neg]
  congr 1
  funext x
  ring

theorem entropy_le_diagonal_potential_integral {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℝ) (ha : IsUnit a) (p : FiniteEntropyDensity (projectionLaw a)) :
    p.entropy ≤ ∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw a := by
  let h := unitProjectionFiniteKLData hn a ha p
  have hg := h.potential_gap_le_entropy_gap
  rw [h.potential_gap_eq_law_integrals, integral_self_potential_eq_entropy] at hg
  change (Spline.diagonalFiniteEntropyDensity n hn).entropy -
    (∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw a) ≤
      (Spline.diagonalFiniteEntropyDensity n hn).entropy - p.entropy at hg
  linarith

def positiveFixedSupportFiniteKLData {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = Real.sqrt (n : ℝ))
    (p : FiniteEntropyDensity (projectionLaw a)) :
    FiniteKLData p (Spline.diagonalFiniteEntropyDensity n hn) := by
  let i : Fin n := ⟨0, by omega⟩
  have hM := projection_density_ae_bound_of_positive_anchor a i (ha i) p
  have hR : projectionRadius a = Real.sqrt (n : ℝ) := by
    unfold projectionRadius
    simp_rw [abs_of_pos (ha _)]
    exact hsum
  exact closedSupportFiniteKLData hn p hM
    ((projectionLaw_ae_mem a).mono fun x hx => by simpa only [hR] using hx)

theorem integrable_potential_of_finiteKL {μ ν : Measure ℝ}
    {p : FiniteEntropyDensity μ} {q : FiniteEntropyDensity ν} (h : FiniteKLData p q) :
    Integrable (fun x => -Real.log (q.density x)) μ := by
  apply (p.integrable_iff_density _).mpr
  convert h.cross_integrable.neg using 1
  funext x
  simp only [Pi.neg_apply]
  ring

theorem integrable_self_potential {μ : Measure ℝ} (p : FiniteEntropyDensity μ) :
    Integrable (fun x => -Real.log (p.density x)) μ := by
  apply (p.integrable_iff_density _).mpr
  convert p.entropy_integrable.neg using 1
  funext x
  simp only [Pi.neg_apply]
  ring

theorem projection_fixedSupport {n : ℕ} (b x : Fin n → ℝ) :
    projection (fixedSupportCoefficients b) x = projection (diagonal n) x + projection b x := by
  simp only [projection, fixedSupportCoefficients, add_mul, Finset.sum_add_distrib]

theorem projectionLaw_normalizedPerturbation_scale {n : ℕ} (b : Fin n → ℝ) :
    (projectionLaw (normalizedPerturbation b)).map
      (fun x => Real.sqrt (1 + perturbationEnergy b) * x) =
        projectionLaw (fixedSupportCoefficients b) := by
  have hc : Real.sqrt (1 + perturbationEnergy b) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith [perturbationEnergy_nonneg b])).ne'
  rw [← projectionLaw_smul]
  congr 1
  funext i
  unfold normalizedPerturbation
  field_simp

theorem entropy_fixedSupport_law {n : ℕ} (hn : 2 ≤ n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {γ : ℝ} (hγ : γ < 1)
    (hbound : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ)
    (p : FiniteEntropyDensity (projectionLaw (normalizedPerturbation b))) :
    p.entropy - (Spline.diagonalFiniteEntropyDensity n hn).entropy ≤
      (∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw (fixedSupportCoefficients b)) -
      (∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw (diagonal n)) -
        Real.log (1 + perturbationEnergy b) / 2 := by
  have hc : 0 < Real.sqrt (1 + perturbationEnergy b) :=
    Real.sqrt_pos.mpr (by linarith [perturbationEnergy_nonneg b])
  let r := (p.scale (Real.sqrt (1 + perturbationEnergy b)) hc).transport
    (projectionLaw_normalizedPerturbation_scale b)
  have hr : r.entropy = p.entropy + Real.log (Real.sqrt (1 + perturbationEnergy b)) := by
    simp only [r, FiniteEntropyDensity.entropy_transport, FiniteEntropyDensity.entropy_scale]
  have hKL := positiveFixedSupportFiniteKLData hn (fixedSupportCoefficients b)
    (fixedSupportCoefficients_pos (by omega) b hγ hbound)
    (fixedSupportCoefficients_sum (by omega) b hb) r
  have hgap := hKL.potential_gap_le_entropy_gap
  rw [hKL.potential_gap_eq_law_integrals] at hgap
  change (∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw (diagonal n)) -
      (∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw (fixedSupportCoefficients b)) ≤
        (Spline.diagonalFiniteEntropyDensity n hn).entropy - r.entropy at hgap
  rw [hr, Real.log_sqrt (by linarith [perturbationEnergy_nonneg b])] at hgap
  linarith

theorem entropy_fixedSupport_cube {n : ℕ} (hn : 2 ≤ n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {γ : ℝ} (hγ : γ < 1)
    (hbound : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ)
    (p : FiniteEntropyDensity (projectionLaw (normalizedPerturbation b))) :
    p.entropy - (Spline.diagonalFiniteEntropyDensity n hn).entropy ≤
      (∫ x, Spline.diagonalSplinePotential n (projection (diagonal n) x + projection b x) -
        Spline.diagonalSplinePotential n (projection (diagonal n) x) ∂cubeLaw n) -
          Real.log (1 + perturbationEnergy b) / 2 := by
  have hc : 0 < Real.sqrt (1 + perturbationEnergy b) :=
    Real.sqrt_pos.mpr (by linarith [perturbationEnergy_nonneg b])
  let r := (p.scale (Real.sqrt (1 + perturbationEnergy b)) hc).transport
    (projectionLaw_normalizedPerturbation_scale b)
  have hKL := positiveFixedSupportFiniteKLData hn (fixedSupportCoefficients b)
    (fixedSupportCoefficients_pos (by omega) b hγ hbound)
    (fixedSupportCoefficients_sum (by omega) b hb) r
  have hVmeas : Measurable (Spline.diagonalSplinePotential n) :=
    (Spline.continuous_diagonalSplineDensity n).measurable.log.neg
  have hi1 : Integrable (Spline.diagonalSplinePotential n) (projectionLaw (fixedSupportCoefficients b)) :=
    integrable_potential_of_finiteKL hKL
  have hi2 : Integrable (Spline.diagonalSplinePotential n) (projectionLaw (diagonal n)) :=
    integrable_self_potential (Spline.diagonalFiniteEntropyDensity n hn)
  have hc1 := (integrable_map_measure hVmeas.aestronglyMeasurable
    (measurable_projection (fixedSupportCoefficients b)).aemeasurable).mp hi1
  have hc2 := (integrable_map_measure hVmeas.aestronglyMeasurable
    (measurable_projection (diagonal n)).aemeasurable).mp hi2
  simp only [Function.comp_def] at hc1 hc2
  have h := entropy_fixedSupport_law hn b hb hγ hbound p
  have hm1 : (∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw (fixedSupportCoefficients b)) =
      ∫ x, Spline.diagonalSplinePotential n (projection (fixedSupportCoefficients b) x) ∂cubeLaw n :=
    integral_map (measurable_projection (fixedSupportCoefficients b)).aemeasurable hVmeas.aestronglyMeasurable
  have hm2 : (∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw (diagonal n)) =
      ∫ x, Spline.diagonalSplinePotential n (projection (diagonal n) x) ∂cubeLaw n :=
    integral_map (measurable_projection (diagonal n)).aemeasurable hVmeas.aestronglyMeasurable
  rw [hm1, hm2, ← integral_sub hc1 hc2] at h
  simpa only [projection_fixedSupport] using h

end
end ENT.Small
