module

public import ENT.Comparison.CurvaturePotential
public import ENT.Comparison.DensityExpectations
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Generic bounded extensions and radial limiting arguments for curvature
potentials. No dimension-specific certificate or density is imported. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace ENT.Comparison

noncomputable section

def clipToRadius (C x : ℝ) : ℝ := max (-C) (min C x)

theorem continuous_clipToRadius (C : ℝ) : Continuous (clipToRadius C) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clipToRadius_mem (C : ℝ) (hC : 0 ≤ C) (x : ℝ) : clipToRadius C x ∈ Icc (-C) C :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clipToRadius_eq (C x : ℝ) (hx : x ∈ Icc (-C) C) : clipToRadius C x = x := by
  unfold clipToRadius
  rw [min_eq_right hx.2, max_eq_right hx.1]

theorem clipToRadius_odd (C : ℝ) (hC : 0 ≤ C) : Function.Odd (clipToRadius C) := by
  intro x
  unfold clipToRadius
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem clipToRadius_hasDerivAt (C x : ℝ) (hx : x ∈ Ioo (-C) C) :
    HasDerivAt (clipToRadius C) 1 x := by
  have heq : clipToRadius C =ᶠ[𝓝 x] id :=
    Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2)
      (fun y hy => clipToRadius_eq C y ⟨hy.1.le, hy.2.le⟩)
  exact (hasDerivAt_id x).congr_of_eventuallyEq heq

namespace CurvaturePotential

def clipped (V : ℝ → ℝ) (ρ C x : ℝ) : ℝ := corrected V (ρ * clipToRadius C x)
def clippedFirst (V : ℝ → ℝ) (ρ C x : ℝ) : ℝ := ρ * correctedFirst V (ρ * clipToRadius C x)
def clippedSecond (V : ℝ → ℝ) (ρ C x : ℝ) : ℝ := ρ ^ 2 * correctedSecond V (ρ * clipToRadius C x)
def clipRadius (R ρ : ℝ) : ℝ := 2 * R / (1 + ρ)

variable {R : ℝ} {V : ℝ → ℝ} (J : CurvaturePotential R V)

include J

theorem scaled_clip_mem (ρ C : ℝ) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hρC : ρ * C < R) (x : ℝ) :
    ρ * clipToRadius C x ∈ Ioo (-R) R := by
  apply abs_lt.mp
  rw [abs_mul, abs_of_nonneg hρ]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr (clipToRadius_mem C hC x)) hρ) hρC

def clippedJet (ρ C : ℝ) (hρ : 0 ≤ ρ) (hC : 0 < C) (hρC : ρ * C < R) :
    EvenJet C (clipped V ρ C) where
  radius_pos := hC
  first := clippedFirst V ρ C
  second := clippedSecond V ρ C
  continuous := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (J.corrected_contDiffAt _ (J.scaled_clip_mem ρ C hρ hC.le hρC x)).continuousAt.comp
      (f := fun y => ρ * clipToRadius C y) (x := x)
      ((continuous_const.mul (continuous_clipToRadius C)).continuousAt)
  first_continuous := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((J.correctedFirst_contDiffAt _ (J.scaled_clip_mem ρ C hρ hC.le hρC x)).continuousAt.comp
      (f := fun y => ρ * clipToRadius C y) (x := x)
      ((continuous_const.mul (continuous_clipToRadius C)).continuousAt)).const_mul ρ
  second_continuous := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((J.correctedSecond_contDiffAt _ (J.scaled_clip_mem ρ C hρ hC.le hρC x)).continuousAt.comp
      (f := fun y => ρ * clipToRadius C y) (x := x)
      ((continuous_const.mul (continuous_clipToRadius C)).continuousAt)).const_mul (ρ ^ 2)
  even := by
    intro x
    unfold clipped
    rw [clipToRadius_odd C hC.le, mul_neg, J.corrected_even]
  first_odd := by
    intro x
    unfold clippedFirst
    rw [clipToRadius_odd C hC.le, mul_neg,
      J.correctedFirst_odd _ (J.scaled_clip_mem ρ C hρ hC.le hρC x)]
    ring
  second_even := by
    intro x
    unfold clippedSecond
    rw [clipToRadius_odd C hC.le, mul_neg,
      J.correctedSecond_even _ (J.scaled_clip_mem ρ C hρ hC.le hρC x)]
  hasDeriv := by
    intro x hx
    have hd := (J.corrected_hasDerivAt _ (J.scaled_clip_mem ρ C hρ hC.le hρC x)).comp x
      ((clipToRadius_hasDerivAt C x hx).const_mul ρ)
    convert hd using 1
    · rfl
    · unfold clippedFirst
      ring
  hasDeriv_first := by
    intro x hx
    have hd := ((J.correctedFirst_hasDerivAt _ (J.scaled_clip_mem ρ C hρ hC.le hρC x)).comp x
      ((clipToRadius_hasDerivAt C x hx).const_mul ρ)).const_mul ρ
    convert hd using 1
    · rfl
    · unfold clippedSecond
      ring
  second_mono := by
    intro x hx y hy hxy
    unfold clippedSecond
    rw [clipToRadius_eq C x ⟨by linarith [hx.1], hx.2⟩,
      clipToRadius_eq C y ⟨by linarith [hy.1], hy.2⟩]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg ρ)
    apply J.correctedSecond_monotone
    · exact ⟨mul_nonneg hρ hx.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hx.2 hρ) hρC⟩
    · exact ⟨mul_nonneg hρ hy.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy.2 hρ) hρC⟩
    · exact mul_le_mul_of_nonneg_left hxy hρ

theorem clipped_bounded (ρ C : ℝ) (hρ : 0 ≤ ρ) (hC : 0 < C) (hρC : ρ * C < R) :
    ∃ M : ℝ, ∀ x, ‖clipped V ρ C x‖ ≤ M := by
  have hc : ContinuousOn (corrected V) (Icc (-(ρ * C)) (ρ * C)) := by
    intro x hx
    exact (J.corrected_contDiffAt x ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun x => hM _ ?_⟩
  have hx := clipToRadius_mem C hC.le x
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hx.1 hρ], mul_le_mul_of_nonneg_left hx.2 hρ⟩

theorem clipRadius_gt (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : R < clipRadius R ρ := by
  have hd : 0 < 1 + ρ := by linarith
  unfold clipRadius
  apply (lt_div_iff₀ hd).mpr
  nlinarith [J.radius_pos]

theorem clipRadius_scaled_lt (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : ρ * clipRadius R ρ < R := by
  have hd : 0 < 1 + ρ := by linarith
  unfold clipRadius
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hd).mpr
  nlinarith [J.radius_pos]

def contractionJet (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    EvenJet (clipRadius R ρ) (clipped V ρ (clipRadius R ρ)) :=
  J.clippedJet ρ (clipRadius R ρ) hρ0 (lt_trans J.radius_pos (J.clipRadius_gt ρ hρ0 hρ1))
    (J.clipRadius_scaled_lt ρ hρ0 hρ1)

theorem contraction_eq (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    EqOn (clipped V ρ (clipRadius R ρ)) (fun x => corrected V (ρ * x)) (Icc (-R) R) := by
  intro x hx
  unfold clipped
  rw [clipToRadius_eq]
  have hr := J.clipRadius_gt ρ hρ0 hρ1
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem contraction_bounded (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ M : ℝ, ∀ x, ‖clipped V ρ (clipRadius R ρ) x‖ ≤ M :=
  J.clipped_bounded ρ (clipRadius R ρ) hρ0 (J.contractionJet ρ hρ0 hρ1).radius_pos
    (J.clipRadius_scaled_lt ρ hρ0 hρ1)

theorem square_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Ioo (-R) R) : Integrable (fun x : ℝ => x ^ 2) μ := by
  apply Integrable.of_bound (measurable_id.pow_const 2).aestronglyMeasurable (R ^ 2)
  apply hμ.mono
  intro x hx
  simp only [id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  have hp : 0 ≤ (R - x) * (R + x) := mul_nonneg (by linarith [hx.2]) (by linarith [hx.1])
  nlinarith

theorem corrected_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Ioo (-R) R) (hV : Integrable V μ) : Integrable (corrected V) μ :=
  hV.add ((J.square_integrable hμ).const_mul (quadraticCorrection V))

theorem integrable_of_ae_bounded_support {μ : Measure ℝ} [IsFiniteMeasure μ]
    (r : ℝ) (hr : r < R) (hμ : ∀ᵐ x ∂μ, x ∈ Icc (-r) r) : Integrable V μ := by
  have hc : ContinuousOn V (Icc (-r) r) := by
    intro x hx
    exact (J.smooth x ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact Integrable.of_bound J.measurable.aestronglyMeasurable M (hμ.mono (fun x hx => hM x hx))

theorem integral_corrected {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Ioo (-R) R) (hV : Integrable V μ) :
    (∫ x, corrected V x ∂μ) = (∫ x, V x ∂μ) + quadraticCorrection V * (∫ x, x ^ 2 ∂μ) := by
  change (∫ x, V x + quadraticCorrection V * x ^ 2 ∂μ) = _
  rw [integral_add hV ((J.square_integrable hμ).const_mul (quadraticCorrection V)), integral_const_mul]

theorem integral_corrected_le_iff {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Ioo (-R) R) (hν : ∀ᵐ x ∂ν, x ∈ Ioo (-R) R)
    (hVμ : Integrable V μ) (hVν : Integrable V ν)
    (hmoment : (∫ x, x ^ 2 ∂μ) = ∫ x, x ^ 2 ∂ν) :
    (∫ x, corrected V x ∂μ) ≤ (∫ x, corrected V x ∂ν) ↔ (∫ x, V x ∂μ) ≤ ∫ x, V x ∂ν := by
  rw [J.integral_corrected hμ hVμ, J.integral_corrected hν hVν, hmoment]
  exact add_le_add_iff_right _

theorem corrected_integral_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ioo (-R) R)
    (hV : Integrable V μ) (ρ : ι → ℝ) (hρbound : ∀ᶠ i in l, ρ i ∈ Icc 0 1)
    (hρlim : Tendsto ρ l (𝓝 1)) :
    Tendsto (fun i => ∫ x, corrected V (ρ i * x) ∂μ) l (𝓝 (∫ x, corrected V x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖corrected V x‖ + ‖corrected V 0‖)
  · exact Filter.Eventually.of_forall (fun i =>
      (J.corrected_measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable)
  · exact hρbound.mono (fun i hi => hμ.mono (fun x hx => J.corrected_contraction_norm_bound (ρ i) x hi hx))
  · exact (J.corrected_integrable hμ hV).norm.add (integrable_const _)
  · apply hμ.mono
    intro x hx
    have hm : Tendsto (fun i => ρ i * x) l (𝓝 x) := by simpa only [one_mul] using hρlim.mul_const x
    exact (J.corrected_contDiffAt x hx).continuousAt.tendsto.comp hm

end CurvaturePotential

theorem curvaturePotential_of_density {μ : Measure ℝ} (q : FiniteEntropyDensity μ)
    (R : ℝ) (hR : 0 < R) (heven : Function.Even q.density)
    (hpos : ∀ x ∈ Ioo (-R) R, 0 < q.density x)
    (hsmooth : ∀ x ∈ Ioo (-R) R, ContDiffAt ℝ 3 q.density x)
    (hthird : ∀ x ∈ Ico 0 R, 0 ≤ deriv (deriv (deriv (fun y => -Real.log (q.density y)))) x) :
    CurvaturePotential R (fun x => -Real.log (q.density x)) where
  radius_pos := hR
  measurable := q.measurable.log.neg
  even := fun x => by
    change -Real.log (q.density (-x)) = -Real.log (q.density x)
    rw [heven x]
  smooth := fun x hx => ((hsmooth x hx).log (ne_of_gt (hpos x hx))).neg
  third_nonneg := hthird

theorem potential_integrable_of_density {μ : Measure ℝ} (q : FiniteEntropyDensity μ) :
    Integrable (fun x => -Real.log (q.density x)) μ := by
  apply (q.integrable_iff_density _).mpr
  apply q.entropy_integrable.neg.congr
  exact Filter.Eventually.of_forall (fun x => by
    simp only [Pi.neg_apply]
    ring)

end
end ENT.Comparison
