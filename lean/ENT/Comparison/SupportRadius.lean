module

public import ENT.Basic.ProjectionSupport
public import ENT.Basic.Coefficients
public import ENT.Comparison.CompactBalancing
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The support radius is at most √n, and equality characterizes the
diagonal coefficient magnitudes. This supplies strict interior support in
the non-diagonal entropy comparison. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT
noncomputable section

theorem projectionRadius_le_sqrt {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    projectionRadius a ≤ Real.sqrt n := by
  change (∑ i, a i ^ 2) = 1 at ha
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => |a i|) (fun _ : Fin n => (1 : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ha, one_mul] at h
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  change (∑ i, |a i|) ≤ Real.sqrt n
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

theorem projectionRadius_eq_sqrt_iff {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    projectionRadius a = Real.sqrt n ↔ IsDiagonal a := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hs : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hcancel : (n : ℝ) * ((Real.sqrt n)⁻¹) ^ 2 = 1 := by
    calc
      _ = (Real.sqrt n) ^ 2 * ((Real.sqrt n)⁻¹) ^ 2 := by rw [hs]
      _ = 1 := by field_simp
  constructor
  · intro hrad
    have hsum : (∑ i, (|a i| - (Real.sqrt n)⁻¹) ^ 2) = 0 := by
      calc
        _ = (∑ i, (a i) ^ 2) - 2 * (Real.sqrt n)⁻¹ * projectionRadius a +
            (n : ℝ) * ((Real.sqrt n)⁻¹) ^ 2 := by
          unfold projectionRadius
          simp_rw [sub_sq, sq_abs]
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          ring
        _ = 0 := by
          rw [ha, hrad, hcancel]
          rw [mul_assoc, inv_mul_cancel₀ hspos.ne']
          norm_num
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (|a i| - (Real.sqrt n)⁻¹))).mp hsum
    apply (isDiagonal_iff_abs a).mpr
    intro i
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hz i (Finset.mem_univ i)))
  · intro hdiag
    have habs := (isDiagonal_iff_abs a).mp hdiag
    unfold projectionRadius
    simp_rw [habs]
    simp only [diagonal, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    calc
      _ = (Real.sqrt n) ^ 2 * (Real.sqrt n)⁻¹ := by rw [hs]
      _ = Real.sqrt n := by field_simp

theorem projectionRadius_lt_sqrt_of_not_diagonal {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : IsUnit a) (hdiag : ¬ IsDiagonal a) :
    projectionRadius a < Real.sqrt n :=
  lt_of_le_of_ne (projectionRadius_le_sqrt a ha)
    (fun h => hdiag ((projectionRadius_eq_sqrt_iff hn a ha).mp h))

namespace Comparison

theorem sqrt_weights_isUnit {n : ℕ} {w : Fin n → ℝ}
    (hw : w ∈ weightSimplex n) : IsUnit (fun i => Real.sqrt (w i)) := by
  unfold IsUnit
  simp_rw [Real.sq_sqrt (hw.1 _)]
  exact hw.2

theorem sum_sqrt_weights_le {n : ℕ} {w : Fin n → ℝ}
    (hw : w ∈ weightSimplex n) : (∑ i, Real.sqrt (w i)) ≤ Real.sqrt n := by
  have h := projectionRadius_le_sqrt _ (sqrt_weights_isUnit hw)
  simpa only [projectionRadius, abs_of_nonneg (Real.sqrt_nonneg _)] using h

end Comparison
end
end ENT
