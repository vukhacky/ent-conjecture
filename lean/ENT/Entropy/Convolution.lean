module

public import ENT.Entropy.Finite
public import ENT.Entropy.LawInvariance
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
Convolution with one bounded compactly supported density.  The other factor may
be any compactly supported probability law, including a Dirac mass.  Finiteness
is proved before the ENNReal-to-real conversion is used in the density identity.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ENT

noncomputable section

def convolutionDensityENNReal (ν : Measure ℝ) (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, f (x - y) ∂ν

theorem measurable_convolutionDensityENNReal (ν : Measure ℝ) [SFinite ν]
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) : Measurable (convolutionDensityENNReal ν f) := by
  have hxy : Measurable (fun z : ℝ × ℝ => f (z.1 - z.2)) := by fun_prop
  exact hxy.lintegral_prod_right'

theorem withDensity_conv_eq (ν : Measure ℝ) [SFinite ν]
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measure.conv (volume.withDensity f) ν =
      volume.withDensity (convolutionDensityENNReal ν f) := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [Measure.lintegral_conv hφ,
    lintegral_withDensity_eq_lintegral_mul volume hf (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul volume
      (measurable_convolutionDensityENNReal ν hf) hφ]
  simp only [Pi.mul_apply, convolutionDensityENNReal]
  calc
    _ = ∫⁻ x, ∫⁻ y, f x * φ (x + y) ∂ν := by
      apply lintegral_congr
      intro x
      rw [lintegral_const_mul _ (by fun_prop)]
    _ = ∫⁻ y, ∫⁻ x, f x * φ (x + y) ∂volume ∂ν :=
      lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ y, ∫⁻ x, f (x - y) * φ x ∂volume ∂ν := by
      apply lintegral_congr
      intro y
      simpa [add_comm] using
        (lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
          (fun x => f (x - y) * φ x) y)
    _ = ∫⁻ x, ∫⁻ y, f (x - y) * φ x ∂ν :=
      (lintegral_lintegral_swap (by fun_prop)).symm
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_mul_const (φ x) (by fun_prop)

def convolutionDensity (ν : Measure ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (convolutionDensityENNReal ν (fun y => ENNReal.ofReal (f y)) x).toReal

theorem measurable_convolutionDensity (ν : Measure ℝ) [SFinite ν]
    {f : ℝ → ℝ} (hf : Measurable f) : Measurable (convolutionDensity ν f) :=
  (measurable_convolutionDensityENNReal ν hf.ennreal_ofReal).ennreal_toReal

theorem convolutionDensity_nonneg (ν : Measure ℝ) (f : ℝ → ℝ) (x : ℝ) :
    0 ≤ convolutionDensity ν f x := ENNReal.toReal_nonneg

theorem convolutionDensityENNReal_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} {M : ℝ} (hM : ∀ x, f x ≤ M) (x : ℝ) :
    convolutionDensityENNReal ν (fun y => ENNReal.ofReal (f y)) x ≤ ENNReal.ofReal M := by
  calc
    _ ≤ ∫⁻ _y, ENNReal.ofReal M ∂ν :=
      lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hM (x - y))
    _ = _ := by simp

theorem convolutionDensity_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, f x ≤ M) (x : ℝ) :
    convolutionDensity ν f x ≤ M :=
  ENNReal.toReal_le_of_le_ofReal hM0 (convolutionDensityENNReal_le ν hM x)

theorem ofReal_convolutionDensity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} {M : ℝ} (hM : ∀ x, f x ≤ M) (x : ℝ) :
    ENNReal.ofReal (convolutionDensity ν f x) =
      convolutionDensityENNReal ν (fun y => ENNReal.ofReal (f y)) x := by
  exact ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (convolutionDensityENNReal_le ν hM x))

theorem withDensity_conv_eq_real (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} {M : ℝ} (hf : Measurable f) (hM : ∀ x, f x ≤ M) :
    Measure.conv (volume.withDensity (fun y => ENNReal.ofReal (f y))) ν =
      volume.withDensity (fun x => ENNReal.ofReal (convolutionDensity ν f x)) := by
  rw [withDensity_conv_eq ν hf.ennreal_ofReal]
  congr 1
  funext x
  exact (ofReal_convolutionDensity ν hM x).symm

theorem convolutionDensity_eq_zero_of_not_mem (ν : Measure ℝ) {f : ℝ → ℝ} {A R : ℝ}
    (hf : ∀ x, x ∉ Set.Icc (-A) A → f x = 0)
    (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (-R) R)
    (x : ℝ) (hx : x ∉ Set.Icc (-(A + R)) (A + R)) :
    convolutionDensity ν f x = 0 := by
  have hzero : (fun y => ENNReal.ofReal (f (x - y))) =ᵐ[ν] 0 := by
    filter_upwards [hν] with y hy
    have hxy : x - y ∉ Set.Icc (-A) A := by
      intro hxy
      apply hx
      constructor <;> linarith [hy.1, hy.2, hxy.1, hxy.2]
    simp only [hf (x - y) hxy, ENNReal.ofReal_zero, Pi.zero_apply]
  have hint : (∫⁻ y, ENNReal.ofReal (f (x - y)) ∂ν) = 0 := by
    rw [lintegral_congr_ae hzero]
    exact lintegral_zero
  simp only [convolutionDensity, convolutionDensityENNReal, hint, ENNReal.toReal_zero]

def convolutionFiniteEntropyDensity {μ : Measure ℝ} (p : FiniteEntropyDensity μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (M A R : ℝ)
    (hM : ∀ x, p.density x ≤ M)
    (hp : ∀ x, x ∉ Set.Icc (-A) A → p.density x = 0)
    (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (-R) R) :
    FiniteEntropyDensity (Measure.conv μ ν) := by
  letI : IsProbabilityMeasure μ := p.isProbabilityMeasure
  have hM0 : 0 ≤ M := (p.nonneg 0).trans (hM 0)
  apply finiteEntropyDensityOfBoundedSupportLaw (Measure.conv μ ν) (convolutionDensity ν p.density)
    M (A + R) (measurable_convolutionDensity ν p.measurable)
    (convolutionDensity_nonneg ν p.density) (convolutionDensity_le ν hM0 hM)
    (convolutionDensity_eq_zero_of_not_mem ν hp hν)
  calc
    Measure.conv μ ν =
        Measure.conv (volume.withDensity (fun x => ENNReal.ofReal (p.density x))) ν :=
      congrArg (fun μ' => Measure.conv μ' ν) p.law_eq
    _ = _ := withDensity_conv_eq_real ν p.measurable hM

end
end ENT
