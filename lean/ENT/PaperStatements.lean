module

public import ENT

/-! The paper's entropy, equality, stability and optimal-limit statements with explicit laws, integrals and coefficient normalization. -/

@[expose] public section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
universe u

namespace ENT.PaperStatements

theorem paper_theorem_1_1 {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hi : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) =
      (2 : ℝ≥0∞)⁻¹ • (volume : Measure ℝ).restrict (Set.Icc (-1) 1))
    (a : Fin n → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    ∃ p q : ℝ → ℝ,
      (∀ x, 0 ≤ p x) ∧ (∀ x, 0 ≤ q x) ∧
      Measurable p ∧ Measurable q ∧
      μ.map (fun ω => ∑ i, a i * U i ω) =
        volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω) =
        volume.withDensity (fun x => ENNReal.ofReal (q x)) ∧
      Integrable (fun x => p x * Real.log (p x)) volume ∧
      Integrable (fun x => q x * Real.log (q x)) volume ∧
      (-(∫ x, p x * Real.log (p x)) ≤ -(∫ x, q x * Real.log (q x))) ∧
      ((-(∫ x, p x * Real.log (p x)) = -(∫ x, q x * Real.log (q x))) ↔
        ∀ i, |a i| = (Real.sqrt (n : ℝ))⁻¹) := by
  obtain ⟨p, q, hle, heq⟩ := ENT.iid_ent_conjecture_ae μ hn U hU hi hlaw a ha
  refine ⟨p.density, q.density, p.nonneg, q.nonneg, p.measurable, q.measurable,
    p.law_eq, q.law_eq, p.entropy_integrable, q.entropy_integrable, hle, ?_⟩
  change p.entropy = q.entropy ↔ _
  rw [heq, ENT.isDiagonal_iff_abs]
  rfl

theorem paper_theorem_1_1_canonical {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    ∃ p q : ℝ → ℝ,
      (∀ x, 0 ≤ p x) ∧ (∀ x, 0 ≤ q x) ∧
      Measurable p ∧ Measurable q ∧
      (Measure.pi (fun _ : Fin n => (2 : ℝ≥0∞)⁻¹ •
        (volume : Measure ℝ).restrict (Set.Icc (-1) 1))).map (fun x => ∑ i, a i * x i) =
        volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      (Measure.pi (fun _ : Fin n => (2 : ℝ≥0∞)⁻¹ •
        (volume : Measure ℝ).restrict (Set.Icc (-1) 1))).map
          (fun x => ∑ i, (Real.sqrt (n : ℝ))⁻¹ * x i) =
        volume.withDensity (fun x => ENNReal.ofReal (q x)) ∧
      Integrable (fun x => p x * Real.log (p x)) volume ∧
      Integrable (fun x => q x * Real.log (q x)) volume ∧
      (-(∫ x, p x * Real.log (p x)) ≤ -(∫ x, q x * Real.log (q x))) ∧
      ((-(∫ x, p x * Real.log (p x)) = -(∫ x, q x * Real.log (q x))) ↔
        ∀ i, |a i| = (Real.sqrt (n : ℝ))⁻¹) := by
  obtain ⟨p, q, hle, heq⟩ := ENT.ent_conjecture n hn a ha
  refine ⟨p.density, q.density, p.nonneg, q.nonneg, p.measurable, q.measurable,
    p.law_eq, q.law_eq, p.entropy_integrable, q.entropy_integrable, hle, ?_⟩
  change p.entropy = q.entropy ↔ _
  rw [heq, ENT.isDiagonal_iff_abs]
  rfl

end ENT.PaperStatements

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace ENT.PaperStatements
noncomputable section

def uniformLaw : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)

def entropy (p : ℝ → ℝ) : ℝ := -(∫ x, p x * Real.log (p x))

def kl (p q : ℝ → ℝ) : ℝ := ∫ x, p x * Real.log (p x / q x)

def deficit {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, ((a i) ^ 2 - (n : ℝ)⁻¹) ^ 2

def IsDensity (μ : Measure ℝ) (p : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ Measurable p ∧ Integrable p volume ∧ (∫ x, p x) = 1 ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      Integrable (fun x => p x * Real.log (p x)) volume

theorem IsDensity.ofBundle {μ : Measure ℝ} (p : ENT.FiniteEntropyDensity μ) :
    IsDensity μ p.density :=
  ⟨p.nonneg, p.measurable, p.integrable, p.mass_one, p.law_eq, p.entropy_integrable⟩

def IsDensity.toBundle {μ : Measure ℝ} {p : ℝ → ℝ} (h : IsDensity μ p) :
    ENT.FiniteEntropyDensity μ :=
  ⟨p, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

def GapBound (μ ν : Measure ℝ) (bound : ℝ) : Prop :=
  ∃ p q : ℝ → ℝ, IsDensity μ p ∧ IsDensity ν q ∧ bound ≤ entropy q - entropy p

def KLGapBound (μ ν : Measure ℝ) (bound : ℝ) : Prop :=
  ∃ p q : ℝ → ℝ, IsDensity μ p ∧ IsDensity ν q ∧
    (∀ᵐ x ∂volume, q x = 0 → p x = 0) ∧
    Integrable (fun x => p x * Real.log (p x / q x)) volume ∧
    bound + kl p q ≤ entropy q - entropy p

theorem KLGapBound.ofBundles {μ ν : Measure ℝ} {bound : ℝ}
    (p : ENT.FiniteEntropyDensity μ) (q : ENT.FiniteEntropyDensity ν)
    (hk : ENT.FiniteKLData p q) (h : bound + hk.klDivergence ≤ q.entropy - p.entropy) :
    KLGapBound μ ν bound := by
  refine ⟨p.density, q.density, IsDensity.ofBundle p, IsDensity.ofBundle q,
    hk.support_ae, hk.integrable_log_ratio, ?_⟩
  rw [hk.klDivergence_eq_log_ratio] at h
  exact h

def weightedLaw {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    (U : Fin n → Ω → ℝ) (a : Fin n → ℝ) : Measure ℝ :=
  μ.map (fun ω => ∑ i, a i * U i ω)

def diagonalLaw {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    (U : Fin n → Ω → ℝ) : Measure ℝ :=
  μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, U i ω)

-- Theorem 1.2, dimensions 3 through 6.
theorem stability_small {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 3 ≤ n) (hn' : n ≤ 6)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hu : ∀ i, μ.map (U i) = uniformLaw)
    (a : Fin n → ℝ) (ha : ∑ i, (a i) ^ 2 = 1) :
    GapBound (weightedLaw μ U a) (diagonalLaw μ U) (deficit a / 1000) := by
  obtain ⟨p, q, h⟩ := ENT.Quantitative.iid_entropy_stability_ge_three_ae μ hn U hU hind hu a ha
  refine ⟨p.density, q.density, IsDensity.ofBundle p, IsDensity.ofBundle q, ?_⟩
  rw [ite_eq_left hn'] at h
  change deficit a / 1000 ≤ q.entropy - p.entropy
  rw [show deficit a = ENT.deficit a from rfl]
  simpa only [div_mul_eq_mul_div₀, one_mul] using h

-- Theorem 1.2, all dimensions >= 7, with the actual KL remainder.
theorem stability_large {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 7 ≤ n)
    (U : Fin n → Ω → ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hu : ∀ i, μ.map (U i) = uniformLaw)
    (a : Fin n → ℝ) (ha : ∑ i, (a i) ^ 2 = 1) :
    KLGapBound (weightedLaw μ U a) (diagonalLaw μ U) (7 * deficit a / (180 * (n : ℝ))) := by
  obtain ⟨p, q, hk, h⟩ := ENT.Quantitative.iid_kl_stability_ge_seven_ae μ hn U hU hind hu a ha
  apply KLGapBound.ofBundles p q hk
  rw [show deficit a = ENT.deficit a from rfl]
  simpa only [div_mul_eq_mul_div₀] using h

-- Theorem 1.2, equation (2), with N depending only on η.
theorem stability_asymptotic (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
    ∀ (U : Fin n → Ω → ℝ), (∀ i, AEMeasurable (U i) μ) →
    iIndepFun U μ → (∀ i, μ.map (U i) = uniformLaw) →
    ∀ (a : Fin n → ℝ), (∑ i, (a i) ^ 2 = 1) →
    KLGapBound (weightedLaw μ U a) (diagonalLaw μ U) ((3/50 - η) * deficit a / (n : ℝ)) := by
  obtain ⟨N, _, hN⟩ := ENT.Quantitative.iid_asymptotic_kl_stability_ae hη
  refine ⟨N, ?_⟩
  intro n hn Ω _ μ _ U hU hind hu a ha
  obtain ⟨p, q, hk, h⟩ := hN n hn μ U hU hind hu a ha
  apply KLGapBound.ofBundles p q hk
  rw [show deficit a = ENT.deficit a from rfl]
  simpa only [div_mul_eq_mul_div₀] using h

def cubeProjectionLaw {n : ℕ} (a : Fin n → ℝ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin n => uniformLaw)).map (fun x => ∑ i, a i * x i)

-- Independent infimum over all unit coefficients and all actual densities.
def slopeSet (n : ℕ) : Set ℝ := { c | ∃ a : Fin n → ℝ,
  (∑ i, (a i) ^ 2 = 1) ∧ 0 < deficit a ∧ ∃ p q : ℝ → ℝ,
    IsDensity (cubeProjectionLaw a) p ∧
    IsDensity (cubeProjectionLaw (fun _ : Fin n => (Real.sqrt (n : ℝ))⁻¹)) q ∧
    c = (n : ℝ) * (entropy q - entropy p) / deficit a }

theorem slopeSet_eq (n : ℕ) (hn : 2 ≤ n) :
    slopeSet n = ENT.Quantitative.entropySlopeSet n := by
  have hn0 : 0 < n := by omega
  ext c
  constructor
  · intro h
    obtain ⟨a, ha, hδ, p, q, hp, hq, hc⟩ := h
    refine ⟨a, ha, hδ, ?_⟩
    let p' : ENT.FiniteEntropyDensity (ENT.projectionLaw a) := hp.toBundle
    let q' : ENT.FiniteEntropyDensity (ENT.projectionLaw (ENT.diagonal n)) := hq.toBundle
    change c = (n : ℝ) * (q'.entropy - p'.entropy) / ENT.deficit a at hc
    unfold ENT.Quantitative.normalizedEntropySlope
    rw [ENT.Quantitative.projectionEntropy_eq a ha p', ENT.Quantitative.diagonalEntropy_eq hn0 q']
    exact hc
  · intro h
    obtain ⟨a, ha, hδ, hc⟩ := h
    obtain ⟨p, q, _⟩ := ENT.ent_conjecture n hn0 a ha
    refine ⟨a, ha, hδ, p.density, q.density, IsDensity.ofBundle p, IsDensity.ofBundle q, ?_⟩
    change c = (n : ℝ) * (q.entropy - p.entropy) / ENT.deficit a
    unfold ENT.Quantitative.normalizedEntropySlope at hc
    rw [ENT.Quantitative.projectionEntropy_eq a ha p, ENT.Quantitative.diagonalEntropy_eq hn0 q] at hc
    exact hc

-- Theorem 1.3, literal infimum limit.
theorem sharp_coefficient_limit :
    Tendsto (fun n => sInf (slopeSet n)) atTop (𝓝 (3/50 : ℝ)) := by
  apply ENT.Quantitative.optimalCoefficient_tendsto.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  change sInf (ENT.Quantitative.entropySlopeSet n) = sInf (slopeSet n)
  rw [slopeSet_eq n hn]

/-- Theorem 3.1 on the actual density of the normalized diagonal sum. -/
theorem diagonal_density_curvature {n : ℕ} (hmin : 7 ≤ n) (hmax : n ≤ 255) :
    ∃ q : ℝ → ℝ,
      IsDensity (cubeProjectionLaw (fun _ : Fin n => (Real.sqrt (n : ℝ))⁻¹)) q ∧
        ∀ x : ℝ, 0 < x → x < Real.sqrt (n : ℝ) →
          7 / (n : ℝ) * x ≤ deriv (deriv (deriv (fun y => -Real.log (q y)))) x := by
  let q := ENT.Spline.diagonalFiniteEntropyDensity n (by omega)
  refine ⟨q.density, IsDensity.ofBundle q, ?_⟩
  intro x hx0 hx1
  exact ENT.Quantitative.actual_density_curvature_seven_through_255 hmin hmax x hx0.le hx1

end
end ENT.PaperStatements
