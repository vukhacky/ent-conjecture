module

public import ENT.Basic.Uniform01
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Finite sums of independent uniforms and their relation to ENT's diagonal law. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT

noncomputable section

def unitCube01 (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => uniform01)

instance unitCube01_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (unitCube01 n) := by
  unfold unitCube01
  infer_instance

def sumProjection01 (n : ℕ) (x : Fin n → ℝ) : ℝ := ∑ i, x i

@[fun_prop]
theorem measurable_sumProjection01 (n : ℕ) : Measurable (sumProjection01 n) := by
  unfold sumProjection01
  fun_prop

def sumLaw01 (n : ℕ) : Measure ℝ := (unitCube01 n).map (sumProjection01 n)

instance sumLaw01_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (sumLaw01 n) := by
  unfold sumLaw01
  infer_instance

@[simp]
theorem sumLaw01_zero : sumLaw01 0 = Measure.dirac 0 := by
  have hsum : sumProjection01 0 = fun _ : Fin 0 → ℝ => 0 := by
    funext x
    simp [sumProjection01]
  simp [sumLaw01, hsum]

@[simp]
theorem sumLaw01_one : sumLaw01 1 = uniform01 := by
  have hsum : sumProjection01 1 = fun x : Fin 1 → ℝ => x 0 := by
    funext x
    simp [sumProjection01]
  rw [sumLaw01, hsum]
  exact (measurePreserving_eval (fun _ : Fin 1 => uniform01) 0).map_eq

theorem sumLaw01_succ (n : ℕ) :
    sumLaw01 (n + 1) = Measure.conv uniform01 (sumLaw01 n) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let f : ℝ × (Fin n → ℝ) → ℝ := fun z => z.1 + sumProjection01 n z.2
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : (unitCube01 (n + 1)).map e = uniform01.prod (unitCube01 n) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => uniform01) 0).map_eq
  have hsum : sumProjection01 (n + 1) = f ∘ e := by
    funext x
    simp [sumProjection01, f, e, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv, Fin.sum_univ_succ, Fin.tail]
  calc
    _ = (uniform01.prod (unitCube01 n)).map f := by
      rw [sumLaw01, hsum, ← Measure.map_map hf e.measurable, he]
    _ = _ := by
      unfold Measure.conv sumLaw01
      have hprod := Measure.map_prod_map uniform01 (unitCube01 n)
        (f := (id : ℝ → ℝ)) (g := sumProjection01 n)
        measurable_id (measurable_sumProjection01 n)
      rw [Measure.map_id] at hprod
      rw [hprod, Measure.map_map (f := Prod.map (id : ℝ → ℝ) (sumProjection01 n))
        (g := fun z : ℝ × ℝ => z.1 + z.2) (by fun_prop) (by fun_prop)]
      rfl

@[simp]
theorem sumLaw01_two : sumLaw01 2 = Measure.conv uniform01 uniform01 := by
  simpa only [sumLaw01_one] using sumLaw01_succ 1

def uniform01ConvolutionPower : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => Measure.conv uniform01 (uniform01ConvolutionPower n)

theorem sumLaw01_eq_convolutionPower (n : ℕ) :
    sumLaw01 n = uniform01ConvolutionPower n := by
  induction n with
  | zero => exact sumLaw01_zero
  | succ n ih => rw [sumLaw01_succ, uniform01ConvolutionPower, ih]

def toUnitCube (n : ℕ) (x : Fin n → ℝ) : Fin n → ℝ := fun i => toUnit (x i)

@[fun_prop]
theorem measurable_toUnitCube (n : ℕ) : Measurable (toUnitCube n) := by
  unfold toUnitCube
  exact measurable_pi_iff.mpr fun i => measurable_toUnit.comp (measurable_pi_apply i)

theorem cubeLaw_map_toUnitCube (n : ℕ) : (cubeLaw n).map (toUnitCube n) = unitCube01 n := by
  unfold cubeLaw unitCube01 toUnitCube
  rw [Measure.pi_map_pi (fun _ : Fin n => measurable_toUnit.aemeasurable)]
  simp only [uniformUnit_map_to_unit]

theorem projectionLaw_diagonal_eq_map_sumLaw01 (n : ℕ) :
    projectionLaw (diagonal n) =
      (sumLaw01 n).map (fun t => ((n : ℝ) - 2 * t) / Real.sqrt (n : ℝ)) := by
  let g : ℝ → ℝ := fun t => ((n : ℝ) - 2 * t) / Real.sqrt (n : ℝ)
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hsum : (cubeLaw n).map (sumProjection01 n ∘ toUnitCube n) = sumLaw01 n := by
    rw [← Measure.map_map (measurable_sumProjection01 n) (measurable_toUnitCube n),
      cubeLaw_map_toUnitCube]
    rfl
  have hproj : projection (diagonal n) = g ∘ (sumProjection01 n ∘ toUnitCube n) := by
    funext x
    simp only [projection, diagonal, Function.comp_apply, sumProjection01, toUnitCube, toUnit,
      ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    dsimp [g]
    ring
  rw [projectionLaw, hproj,
    ← Measure.map_map hg ((measurable_sumProjection01 n).comp (measurable_toUnitCube n)), hsum]

universe u

theorem sum_iid_uniform01_eq_sumLaw01 {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (U : Fin n → Ω → ℝ)
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = uniform01) :
    μ.map (fun ω => ∑ i, U i ω) = sumLaw01 n := by
  have hjoint : Measurable (fun ω i => U i ω) := Measurable.of_eval hU
  have hmap : μ.map (fun ω i => U i ω) = unitCube01 n := by
    rw [iIndepFun.map_fun_eq_pi_map (fun i => (hU i).aemeasurable) hind]
    simp only [hlaw, unitCube01]
  change μ.map (sumProjection01 n ∘ (fun ω i => U i ω)) = _
  rw [← Measure.map_map (measurable_sumProjection01 n) hjoint, hmap]
  rfl

end
end ENT
