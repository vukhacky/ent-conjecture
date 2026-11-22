module

public import ENT.Pang.SineSum
public import ENT.Spline.DensityLaw
public import ENT.Entropy.Convolution
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Tactic.FieldSimp

/-! Exponential tilting commutes with independent summation. The tilted sum has a density given by an exponential multiple of the uniform-sum spline density. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators ENNReal

namespace ENT.Pang

noncomputable section

universe u v

theorem map_withDensity_comp {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    {f : α → β} {w : β → ℝ≥0∞} (hf : Measurable f) (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ hf]
  change (∫⁻ a, (φ ∘ f) a ∂μ.withDensity (w ∘ f)) = _
  rw [
    lintegral_withDensity_eq_lintegral_mul μ (hw.comp hf) (hφ.comp hf),
    lintegral_withDensity_eq_lintegral_mul (μ.map f) hw hφ,
    lintegral_map (hw.mul hφ) hf]
  rfl

def exponentialWeight (c t x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (c * Real.exp (t * x))

theorem measurable_exponentialWeight (c t : ℝ) : Measurable (exponentialWeight c t) := by
  unfold exponentialWeight
  fun_prop

theorem exponentialWeight_add {c d : ℝ} (hc : 0 ≤ c) (_hd : 0 ≤ d)
    (t x y : ℝ) :
    exponentialWeight c t x * exponentialWeight d t y =
      exponentialWeight (c * d) t (x + y) := by
  unfold exponentialWeight
  rw [← ENNReal.ofReal_mul (by positivity), mul_add, Real.exp_add]
  congr 1
  ring

theorem conv_exponentialWeight (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (t : ℝ) :
    Measure.conv (μ.withDensity (exponentialWeight c t))
      (ν.withDensity (exponentialWeight d t)) =
      (Measure.conv μ ν).withDensity (exponentialWeight (c * d) t) := by
  unfold Measure.conv
  rw [prod_withDensity (measurable_exponentialWeight c t) (measurable_exponentialWeight d t)]
  have hweight : (fun z : ℝ × ℝ => exponentialWeight c t z.1 * exponentialWeight d t z.2) =
      exponentialWeight (c * d) t ∘ (fun z : ℝ × ℝ => z.1 + z.2) := by
    funext z
    exact exponentialWeight_add hc hd t z.1 z.2
  rw [hweight]
  exact map_withDensity_comp (μ.prod ν) (by fun_prop) (measurable_exponentialWeight (c * d) t)

def iidSumLaw (μ : Measure ℝ) (n : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin n => μ)).map (sumProjection01 n)

instance iidSumLaw_isProbabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (iidSumLaw μ n) := by
  unfold iidSumLaw
  infer_instance

@[simp]
theorem iidSumLaw_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    iidSumLaw μ 0 = Measure.dirac 0 := by
  have hsum : sumProjection01 0 = fun _ : Fin 0 → ℝ => 0 := by
    funext x
    simp [sumProjection01]
  simp [iidSumLaw, hsum]

theorem iidSumLaw_succ (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    iidSumLaw μ (n + 1) = Measure.conv μ (iidSumLaw μ n) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let f : ℝ × (Fin n → ℝ) → ℝ := fun z => z.1 + sumProjection01 n z.2
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : (Measure.pi (fun _ : Fin (n + 1) => μ)).map e =
      μ.prod (Measure.pi (fun _ : Fin n => μ)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).map_eq
  have hsum : sumProjection01 (n + 1) = f ∘ e := by
    funext x
    simp [sumProjection01, f, e, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv, Fin.sum_univ_succ, Fin.tail]
  calc
    _ = (μ.prod (Measure.pi (fun _ : Fin n => μ))).map f := by
      rw [iidSumLaw, hsum, ← Measure.map_map hf e.measurable, he]
    _ = _ := by
      unfold Measure.conv iidSumLaw
      have hprod := Measure.map_prod_map μ (Measure.pi (fun _ : Fin n => μ))
        (f := (id : ℝ → ℝ)) (g := sumProjection01 n)
        measurable_id (measurable_sumProjection01 n)
      rw [Measure.map_id] at hprod
      rw [hprod, Measure.map_map (f := Prod.map (id : ℝ → ℝ) (sumProjection01 n))
        (g := fun z : ℝ × ℝ => z.1 + z.2) (by fun_prop) (by fun_prop)]
      rfl

def tiltNormalizer (t : ℝ) : ℝ := t / Real.sinh t

theorem tiltNormalizer_pos {t : ℝ} (ht : 0 < t) : 0 < tiltNormalizer t :=
  div_pos ht (Real.sinh_pos_iff.mpr ht)

theorem tiltLaw_eq_exponentialWeight {t : ℝ} (ht : 0 < t) :
    tiltLaw t = uniformUnit.withDensity (exponentialWeight (tiltNormalizer t) t) := by
  rw [uniformDensity_law, ← withDensity_mul _
    (measurable_uniformDensity.ennreal_ofReal) (measurable_exponentialWeight _ _)]
  unfold tiltLaw
  congr 1
  funext x
  simp only [Pi.mul_apply]
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · simp only [tiltDensity, uniformDensity, Set.indicator_of_mem hx,
      exponentialWeight, tiltWeight, tiltNormalizer]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  · simp only [tiltDensity, uniformDensity, Set.indicator_of_notMem hx,
      ENNReal.ofReal_zero, zero_mul]

theorem iidSumLaw_tilt {t : ℝ} (ht : 0 < t) (n : ℕ) :
    iidSumLaw (tiltLaw t) n =
      (iidSumLaw uniformUnit n).withDensity (exponentialWeight ((tiltNormalizer t) ^ n) t) := by
  let := isProbabilityMeasure_tiltLaw ht
  induction n with
  | zero =>
      rw [iidSumLaw_zero, iidSumLaw_zero, dirac_withDensity]
      simp [exponentialWeight]
  | succ n ih =>
      rw [iidSumLaw_succ, iidSumLaw_succ, ih, tiltLaw_eq_exponentialWeight ht,
        conv_exponentialWeight _ _ (tiltNormalizer_pos ht).le
          (pow_nonneg (tiltNormalizer_pos ht).le n)]
      rw [pow_succ']

theorem iidSumLaw_uniform_map_normalize (n : ℕ) :
    (iidSumLaw uniformUnit n).map (fun x => (Real.sqrt (n : ℝ))⁻¹ * x) =
      projectionLaw (diagonal n) := by
  rw [iidSumLaw, Measure.map_map (by fun_prop) (measurable_sumProjection01 n)]
  congr 1
  funext x
  simp only [Function.comp_apply, sumProjection01, projection, diagonal, ← Finset.mul_sum]

def tiltedDiagonalLaw (n : ℕ) (t : ℝ) : Measure ℝ :=
  (iidSumLaw (tiltLaw t) n).map (fun x => (Real.sqrt (n : ℝ))⁻¹ * x)

theorem tiltedDiagonalLaw_eq {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) :
    tiltedDiagonalLaw n t =
      (projectionLaw (diagonal n)).withDensity
        (exponentialWeight ((tiltNormalizer t) ^ n) (t * Real.sqrt (n : ℝ))) := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hn)
  have hw : exponentialWeight ((tiltNormalizer t) ^ n) t =
      exponentialWeight ((tiltNormalizer t) ^ n) (t * Real.sqrt (n : ℝ)) ∘
        (fun x => (Real.sqrt (n : ℝ))⁻¹ * x) := by
    funext x
    unfold exponentialWeight
    congr 2
    dsimp
    field_simp
  rw [tiltedDiagonalLaw, iidSumLaw_tilt ht, hw,
    map_withDensity_comp _ (by fun_prop) (measurable_exponentialWeight _ _),
    iidSumLaw_uniform_map_normalize]

end
end ENT.Pang
