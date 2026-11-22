module

public import ENT.Comparison.UniformAverage
public import ENT.Comparison.EvenJet
public import ENT.Basic.ProjectionDensity

/-! Convolution with a centered uniform law preserves even unimodality. Monotonicity follows by comparing translated strips of a sliding interval. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace ENT.Comparison
noncomputable section

def IsEvenUnimodal (g : ℝ → ℝ) : Prop :=
  Function.Even g ∧ AntitoneOn g (Ici 0)

theorem uniformAverage_eq_interval_measurable {c : ℝ} (hc : 0 < c)
    {g : ℝ → ℝ} (hg : Measurable g) (x : ℝ) :
    uniformAverage c g x = (∫ y in x-c..x+c, g y)/(2*c) := by
  have hmap := integral_map (μ := uniformUnit) (measurable_const_mul c).aemeasurable
    (f := fun y => g (x+y)) (hg.comp (by fun_prop)).aestronglyMeasurable
  rw [uniformUnit_map_mul_pos hc, integral_smul_measure] at hmap
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*c)⁻¹), smul_eq_mul] at hmap
  unfold uniformAverage
  rw [← hmap, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -c ≤ c),
    intervalIntegral.integral_comp_add_left]
  rw [show x + -c = x-c by ring]
  ring

theorem uniformAverage_even_measurable {g : ℝ → ℝ} (hg : Measurable g)
    (heven : Function.Even g) (c x : ℝ) : uniformAverage c g (-x) = uniformAverage c g x := by
  have hmap := integral_map (μ := uniformUnit) measurable_neg.aemeasurable
    (f := fun u => g (-x+c*u)) (hg.comp (by fun_prop)).aestronglyMeasurable
  rw [uniformUnit_map_neg] at hmap
  unfold uniformAverage
  rw [hmap]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    change g (-x+c*(-u)) = g (x+c*u)
    rw [show -x+c*(-u) = -(x+c*u) by ring, heven]

theorem sliding_interval_antitone {g : ℝ → ℝ} (hg : Integrable g volume)
    (heven : Function.Even g) (hmono : AntitoneOn g (Ici 0)) {c : ℝ} (hc : 0 ≤ c) :
    AntitoneOn (fun x => ∫ t in x-c..x+c, g t) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hshift : (∫ t in x-c..y-c, g (t+2*c)) = (∫ t in x+c..y+c, g t) := by
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring
  have hgi : IntervalIntegrable (fun t => g (t+2*c)) volume (x-c) (y-c) := by
    convert (hg.intervalIntegrable (a := x+c) (b := y+c)).comp_add_right (2*c) using 1 <;> ring
  have hstrip := intervalIntegral.integral_mono_on (by linarith : x-c ≤ y-c)
    hgi hg.intervalIntegrable (fun t ht => by
      have htc : 0 ≤ t+2*c := by linarith [ht.1,hx]
      have habs : |t| ≤ |t+2*c| := by
        rw [abs_of_nonneg htc]
        exact abs_le.mpr ⟨by linarith [ht.1,hx],by linarith⟩
      have h := hmono (abs_nonneg t) (abs_nonneg (t+2*c)) habs
      simpa only [even_apply_abs heven] using h)
  rw [hshift] at hstrip
  have hcomm := intervalIntegral.integral_interval_sub_interval_comm
    (hg.intervalIntegrable (a := x-c) (b := x+c))
    (hg.intervalIntegrable (a := y-c) (b := y+c))
    (hg.intervalIntegrable (a := x-c) (b := y-c))
  linarith

theorem IsEvenUnimodal.uniformAverage {g : ℝ → ℝ} (h : IsEvenUnimodal g)
    (hg : Measurable g) (hgi : Integrable g volume) {c : ℝ} (hc : 0 ≤ c) :
    IsEvenUnimodal (uniformAverage c g) := by
  refine ⟨uniformAverage_even_measurable hg h.1 c, ?_⟩
  by_cases hc0 : c = 0
  · simpa only [hc0, funext (uniformAverage_zero g)] using h.2
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    intro x hx y hy hxy
    rw [uniformAverage_eq_interval_measurable hcp hg,
      uniformAverage_eq_interval_measurable hcp hg]
    exact div_le_div_of_nonneg_right
      (sliding_interval_antitone hgi h.1 h.2 hc hx hy hxy) (by positivity)

theorem scaledUniformDensity_even_unimodal {c : ℝ} (hc : 0 < c) :
    IsEvenUnimodal (scaledUniformDensity c) := by
  constructor
  · intro x
    have hmem : -x ∈ Icc (-c) c ↔ x ∈ Icc (-c) c := by
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    by_cases hx : x ∈ Icc (-c) c
    · simp only [scaledUniformDensity, indicator_of_mem hx, indicator_of_mem (hmem.mpr hx)]
    · simp only [scaledUniformDensity, indicator_of_notMem hx,
        indicator_of_notMem (not_congr hmem |>.mpr hx)]
  · intro x hx y hy hxy
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    by_cases hyc : y ∈ Icc (-c) c
    · have hxc : x ∈ Icc (-c) c := ⟨by linarith [hx],hxy.trans hyc.2⟩
      simp only [scaledUniformDensity, indicator_of_mem hyc, indicator_of_mem hxc, le_refl]
    · rw [scaledUniformDensity_eq_zero_of_not_mem c y hyc]
      exact scaledUniformDensity_nonneg hc x

end
end ENT.Comparison
