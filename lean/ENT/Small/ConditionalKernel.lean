module

public import ENT.Basic.Exchangeability
public import ENT.Small.LocalGeometry

/-! Actual weighted second moments on the cube. This supplies the covariance
part of the conditional variance argument without introducing a conditional
distribution as an unproved premise. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ENT.Small
noncomputable section

theorem exists_perm_map_two {α : Type*} [DecidableEq α] (i j k l : α)
    (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ e : Equiv.Perm α, e i = k ∧ e j = l := by
  let e₁ := Equiv.swap i k
  have hj : e₁ j ≠ k := by
    intro h
    have hi : e₁ i = k := Equiv.swap_apply_left i k
    exact hij (e₁.injective (hi.trans h.symm))
  let e₂ := Equiv.swap (e₁ j) l
  refine ⟨e₁.trans e₂, ?_, ?_⟩
  · change e₂ (e₁ i) = k
    rw [show e₁ i = k from Equiv.swap_apply_left i k]
    exact Equiv.swap_apply_of_ne_of_ne hj.symm hkl
  · change e₂ (e₁ j) = l
    exact Equiv.swap_apply_left _ _

def diagonalTestMoment {n : ℕ} (f : ℝ → ℝ) (i j : Fin n) : ℝ :=
  ∫ x : Fin n → ℝ, (x i * x j) * f (projection (diagonal n) x) ∂cubeLaw n

theorem diagonalTestMoment_perm {n : ℕ} (f : ℝ → ℝ) (e : Equiv.Perm (Fin n))
    (i j : Fin n) : diagonalTestMoment f (e i) (e j) = diagonalTestMoment f i j := by
  have h := (measurePreserving_coordinatePermutation e).integral_comp'
    (fun x : Fin n → ℝ => (x i * x j) * f (projection (diagonal n) x))
  simpa only [diagonalTestMoment, coordinatePermutation_apply,
    projection_diagonal_coordinatePermutation] using h

theorem integrable_coordinate_pair_diagonal_test {n : ℕ} (i j : Fin n) {f : ℝ → ℝ}
    (hf : Integrable (fun x => f (projection (diagonal n) x)) (cubeLaw n)) :
    Integrable (fun x : Fin n → ℝ => (x i * x j) * f (projection (diagonal n) x))
      (cubeLaw n) := by
  have h := (integrable_coordinate_diagonal_test j hf).bdd_mul
    (measurable_pi_apply i).aestronglyMeasurable
    ((cubeLaw_ae_mem n).mono fun x hx => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr (hx i))
  simpa only [mul_assoc] using h

theorem diagonalTestMoment_eq {n : ℕ} (f : ℝ → ℝ) (i₀ i₁ : Fin n) (hne : i₀ ≠ i₁)
    (i j : Fin n) :
    diagonalTestMoment f i j = diagonalTestMoment f i₀ i₁ +
      if i = j then diagonalTestMoment f i₀ i₀ - diagonalTestMoment f i₀ i₁ else 0 := by
  by_cases hij : i = j
  · subst j
    have h := diagonalTestMoment_perm f (Equiv.swap i i₀) i i
    simp only [Equiv.swap_apply_left] at h
    simp only [ite_true]
    linarith
  · obtain ⟨e, hei, hej⟩ := exists_perm_map_two i j i₀ i₁ hij hne
    have h := diagonalTestMoment_perm f e i j
    rw [hei, hej] at h
    simpa only [if_neg hij, add_zero] using h.symm

theorem quadratic_matrix_sum {n : ℕ} (b : Fin n → ℝ) (A B : ℝ) :
    (∑ i, ∑ j, b i * b j * (B + if i = j then A - B else 0)) =
      (A - B) * perturbationEnergy b + B * (∑ i, b i) ^ 2 := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hdiag : (∑ i, ∑ j, b i * b j * (if i = j then A - B else 0)) =
      (A - B) * perturbationEnergy b := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    unfold perturbationEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiag]
  have hconst : (∑ i, ∑ j, b i * b j * B) = B * (∑ i, b i) ^ 2 := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hconst]
  ring

theorem integral_projection_sq_diagonal_test {n : ℕ} (b : Fin n → ℝ)
    (i₀ i₁ : Fin n) (hne : i₀ ≠ i₁) {f : ℝ → ℝ}
    (hf : Integrable (fun x => f (projection (diagonal n) x)) (cubeLaw n)) :
    (∫ x, projection b x ^ 2 * f (projection (diagonal n) x) ∂cubeLaw n) =
      (diagonalTestMoment f i₀ i₀ - diagonalTestMoment f i₀ i₁) * perturbationEnergy b +
        diagonalTestMoment f i₀ i₁ * (∑ i, b i) ^ 2 := by
  have hfun : (fun x : Fin n → ℝ => projection b x ^ 2 * f (projection (diagonal n) x)) =
      (fun x => ∑ i, ∑ j, b i * b j * ((x i * x j) * f (projection (diagonal n) x))) := by
    funext x
    simp only [projection, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hint (i j : Fin n) : Integrable
      (fun x => b i * b j * ((x i * x j) * f (projection (diagonal n) x))) (cubeLaw n) :=
    (integrable_coordinate_pair_diagonal_test i j hf).const_mul _
  calc
    _ = ∑ i, ∑ j, b i * b j * diagonalTestMoment f i j := by
      rw [hfun, integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        · simp only [integral_const_mul, diagonalTestMoment]
        · intro j _
          exact hint i j
      · intro i _
        exact integrable_finsetSum _ fun j _ => hint i j
    _ = ∑ i, ∑ j, b i * b j * (diagonalTestMoment f i₀ i₁ +
        if i = j then diagonalTestMoment f i₀ i₀ - diagonalTestMoment f i₀ i₁ else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [diagonalTestMoment_eq f i₀ i₁ hne i j]
    _ = _ := quadratic_matrix_sum b _ _

theorem integral_zero_sum_projection_sq_diagonal_test {n : ℕ} (hn : 2 ≤ n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) {f : ℝ → ℝ}
    (hf : Integrable (fun x => f (projection (diagonal n) x)) (cubeLaw n)) :
    (∫ x, projection b x ^ 2 * f (projection (diagonal n) x) ∂cubeLaw n) =
      perturbationEnergy b / ((n : ℝ) - 1) *
        ((n : ℝ) * diagonalTestMoment (n := n) f ⟨0, by omega⟩ ⟨0, by omega⟩ -
          ∫ x, projection (diagonal n) x ^ 2 * f (projection (diagonal n) x) ∂cubeLaw n) := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by intro h; have := congrArg Fin.val h; norm_num [i₀, i₁] at this
  have hbformula := integral_projection_sq_diagonal_test b i₀ i₁ hne hf
  rw [hb, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hbformula
  have hdformula := integral_projection_sq_diagonal_test (diagonal n) i₀ i₁ hne hf
  have hdenergy : perturbationEnergy (diagonal n) = 1 := isUnit_diagonal (by omega)
  rw [hdenergy, mul_one, sum_diagonal (by omega), Real.sq_sqrt (Nat.cast_nonneg n)] at hdformula
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [hbformula, hdformula]
  change (diagonalTestMoment f i₀ i₀ - diagonalTestMoment f i₀ i₁) * perturbationEnergy b = _
  field_simp
  ring

end
end ENT.Small
