module

public import ENT.Basic.ProjectionSupport
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Coordinate exchangeability of the canonical product law and the vanishing
of every integrable diagonal test against a zero-sum linear perturbation. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace ENT

noncomputable section

def coordinatePermutation {n : ℕ} (e : Equiv.Perm (Fin n)) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm

@[simp]
theorem coordinatePermutation_apply {n : ℕ} (e : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (i : Fin n) : coordinatePermutation e x i = x (e i) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) e.symm x (e i)
  simpa only [coordinatePermutation, Equiv.symm_apply_apply] using h

theorem measurePreserving_coordinatePermutation {n : ℕ} (e : Equiv.Perm (Fin n)) :
    MeasurePreserving (coordinatePermutation e) (cubeLaw n) (cubeLaw n) :=
  measurePreserving_piCongrLeft (fun _ : Fin n => uniformUnit) e.symm

theorem projection_diagonal_coordinatePermutation {n : ℕ} (e : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) : projection (diagonal n) (coordinatePermutation e x) = projection (diagonal n) x := by
  simp only [projection, diagonal, coordinatePermutation_apply, ← Finset.mul_sum]
  rw [Equiv.sum_comp e]

theorem projectionLaw_permutation {n : ℕ} (a : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    projectionLaw (fun i => a (e i)) = projectionLaw a := by
  have heq : projection (fun i => a (e i)) = projection a ∘ coordinatePermutation e.symm := by
    funext x
    simp only [projection, Function.comp_apply, coordinatePermutation_apply]
    have h := Equiv.sum_comp e (fun i => a i * x (e.symm i))
    simpa only [Equiv.symm_apply_apply] using h
  rw [projectionLaw, heq, ← Measure.map_map (measurable_projection a)
    (coordinatePermutation e.symm).measurable,
    (measurePreserving_coordinatePermutation e.symm).map_eq]
  rfl

theorem integral_coordinate_diagonal_test_eq {n : ℕ} (i j : Fin n) (f : ℝ → ℝ) :
    (∫ x : Fin n → ℝ, x i * f (projection (diagonal n) x) ∂cubeLaw n) =
      ∫ x : Fin n → ℝ, x j * f (projection (diagonal n) x) ∂cubeLaw n := by
  have h := (measurePreserving_coordinatePermutation (Equiv.swap i j)).integral_comp'
    (fun x : Fin n → ℝ => x i * f (projection (diagonal n) x))
  simp only [coordinatePermutation_apply, Equiv.swap_apply_left,
    projection_diagonal_coordinatePermutation] at h
  exact h.symm

theorem integrable_coordinate_diagonal_test {n : ℕ} (i : Fin n) {f : ℝ → ℝ}
    (hf : Integrable (fun x => f (projection (diagonal n) x)) (cubeLaw n)) :
    Integrable (fun x : Fin n → ℝ => x i * f (projection (diagonal n) x)) (cubeLaw n) := by
  apply hf.bdd_mul (measurable_pi_apply i).aestronglyMeasurable
  exact (cubeLaw_ae_mem n).mono fun x hx => by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (hx i)

theorem integral_zero_sum_projection_diagonal_test {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {f : ℝ → ℝ}
    (hf : Integrable (fun x => f (projection (diagonal n) x)) (cubeLaw n)) :
    (∫ x, projection b x * f (projection (diagonal n) x) ∂cubeLaw n) = 0 := by
  let i₀ : Fin n := ⟨0, hn⟩
  have heq : (fun x => projection b x * f (projection (diagonal n) x)) =
      (fun x : Fin n → ℝ => ∑ i, b i * (x i * f (projection (diagonal n) x))) := by
    funext x
    simp only [projection, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_finsetSum]
  · simp_rw [integral_const_mul, integral_coordinate_diagonal_test_eq (j := i₀)]
    rw [← Finset.sum_mul, hb, zero_mul]
  · intro i hi
    exact (integrable_coordinate_diagonal_test i hf).const_mul (b i)

end
end ENT
