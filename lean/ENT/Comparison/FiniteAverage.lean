module

public import ENT.Comparison.EvenJet
public import ENT.Basic.ProjectionConvolution
public import Mathlib.MeasureTheory.Integral.Prod

/-! Finite residual sums as iterated averages of actual independent continuous
uniform variables. All uses of Fubini have a bounded-integrable witness. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace ENT.Comparison
noncomputable section

def finiteAverage {n : ℕ} (g : ℝ → ℝ) (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∫ y, g (x + projection a y) ∂cubeLaw n

theorem finiteAverage_norm_le {n : ℕ} {g : ℝ → ℝ} {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) (a : Fin n → ℝ) (x : ℝ) :
    ‖finiteAverage g a x‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := cubeLaw n)
    (Filter.Eventually.of_forall (fun y => hC (x + projection a y)))
  simpa [finiteAverage, measureReal_def] using h

theorem continuous_finiteAverage {n : ℕ} {g : ℝ → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (a : Fin n → ℝ) :
    Continuous (finiteAverage g a) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro x
    exact (hg.comp (continuous_const.add (continuous_projection a))).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun y => hC (x + projection a y))
  · exact integrable_const C
  · apply Filter.Eventually.of_forall
    intro y
    exact hg.comp (continuous_id.add_const _)

@[simp] theorem finiteAverage_empty (g : ℝ → ℝ) (a : Fin 0 → ℝ) (x : ℝ) :
    finiteAverage g a x = g x := by
  simp [finiteAverage, projection]

theorem potentialExpectation_eq_finiteAverage {n : ℕ} (g : ℝ → ℝ)
    (a : Fin n → ℝ) : potentialExpectation g a = finiteAverage g a 0 := by
  simp [potentialExpectation, finiteAverage]

theorem finiteAverage_remove {n : ℕ} {g : ℝ → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (a : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    finiteAverage g a = uniformAverage (a i) (finiteAverage g (removeCoefficient a i)) := by
  funext x
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let f : ℝ × (Fin n → ℝ) → ℝ :=
    fun z => g (x + a i * z.1 + projection (removeCoefficient a i) z.2)
  have hfcont : Continuous f := hg.comp
    ((continuous_const.add (continuous_const.mul continuous_fst)).add
      ((continuous_projection (removeCoefficient a i)).comp continuous_snd))
  have hf : Integrable f (uniformUnit.prod (cubeLaw n)) :=
    Integrable.of_bound hfcont.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun z => hC _))
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => uniformUnit) i).integral_comp' f
  change (∫ y, f (e y) ∂cubeLaw (n + 1)) =
    ∫ z, f z ∂uniformUnit.prod (cubeLaw n) at he
  have hpoint (y : Fin (n + 1) → ℝ) : g (x + projection a y) = f (e y) := by
    simp only [f, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
      removeCoefficient, projection]
    change g (x + ∑ j, a j * y j) =
      g (x + a i * y i + ∑ j, a (i.succAbove j) * y (i.succAbove j))
    rw [Fin.sum_univ_succAbove (fun j => a j * y j) i]
    congr 1
    ring
  change (∫ y, g (x + projection a y) ∂cubeLaw (n + 1)) = _
  simp_rw [hpoint]
  rw [he, integral_prod f hf]
  rfl

theorem finiteAverage_two {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) (a b : ℝ) :
    finiteAverage g ![a, b] = uniformAverage a (uniformAverage b g) := by
  rw [finiteAverage_remove hg hC _ 0]
  rw [finiteAverage_remove hg hC _ 0]
  simp only [removeCoefficient, Fin.succAbove_zero, Fin.succ_zero_eq_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  congr 1
  congr 1
  funext x
  exact finiteAverage_empty _ _ _

namespace EvenJet

/-- Averaging any finite family of nonnegative coefficients preserves the
jet class on the interval shortened by their sum. Zero coefficients are
handled by the exact identity for the probability average. -/
def finite_average {R : ℝ} {g : ℝ → ℝ} (J : EvenJet R g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hR : (∑ i, a i) < R) :
    EvenJet (R - ∑ i, a i) (finiteAverage g a) := by
  induction n with
  | zero =>
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
      funext (finiteAverage_empty g a)] using J
  | succ n ih =>
    let r := removeCoefficient a 0
    have hr : ∀ i, 0 ≤ r i := fun i => ha _
    have hsum : (∑ i, a i) = a 0 + ∑ i, r i := by
      exact Fin.sum_univ_succAbove a 0
    have hrR : (∑ i, r i) < R := by linarith [ha 0]
    have K := ih r hr hrR
    rw [finiteAverage_remove J.continuous hC a 0, hsum]
    by_cases hb : a 0 = 0
    · have hzero (f : ℝ → ℝ) : uniformAverage 0 f = f :=
        funext (uniformAverage_zero _)
      simpa only [hb, zero_add, hzero] using K
    · have hbpos : 0 < a 0 := lt_of_le_of_ne (ha 0) (Ne.symm hb)
      have hbR : a 0 < R - ∑ i, r i := by linarith
      have L := K.average hbpos hbR (finiteAverage_norm_le hC r)
      convert L using 1 <;> ring

end EvenJet
end
end ENT.Comparison
