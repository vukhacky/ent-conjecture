module

public import ENT.Small.LocalConstants
public import ENT.Small.ConditionalKernelLaw
public import ENT.Spline.PositiveInterior
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic.FieldSimp

/-! Exact affine derivative transport from the unit-sum spline to the genuine
normalized diagonal potential. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology

namespace ENT.Small
noncomputable section

theorem iteratedDeriv_affine_real (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) :
    iteratedDeriv k (fun x => f (a * x + b)) =
      fun x => a ^ k * iteratedDeriv k f (a * x + b) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [deriv_const_mul_field]
      have h := deriv_comp_mul_left a (fun z => iteratedDeriv k f (z + b)) x
      rw [deriv_comp_add_const] at h
      rw [h]
      simp only [smul_eq_mul, iteratedDeriv_succ, pow_succ]
      ring

theorem diagonalPotential_eq_affine_log (n : ℕ) (hn : 2 ≤ n) {x : ℝ}
    (hx : x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    Spline.diagonalSplinePotential n x =
      -Real.log (Real.sqrt (n : ℝ) / 2) - Real.log
        (Spline.unitSumSplineDensity n ((-Real.sqrt (n : ℝ) / 2) * x + (n : ℝ) / 2)) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hq := Spline.diagonalSplineDensity_pos n hn x hx
  unfold Spline.diagonalSplineDensity at hq
  have harg : ((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2 =
      (-Real.sqrt (n : ℝ) / 2) * x + (n : ℝ) / 2 := by ring
  have hf : Spline.unitSumSplineDensity n (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hq
    exact (lt_irrefl (0 : ℝ)) hq
  unfold Spline.diagonalSplinePotential Spline.diagonalSplineDensity
  rw [Real.log_mul (by positivity : Real.sqrt (n : ℝ) / 2 ≠ 0) hf, harg]
  ring

theorem diagonalPotential_iteratedDeriv (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    iteratedDeriv k (Spline.diagonalSplinePotential n) x =
      -(-Real.sqrt (n : ℝ) / 2) ^ k *
        iteratedDeriv k (fun t => Real.log (Spline.unitSumSplineDensity n t))
          (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2) := by
  have heq : Spline.diagonalSplinePotential n =ᶠ[𝓝 x] fun y =>
      -Real.log (Real.sqrt (n : ℝ) / 2) - Real.log
        (Spline.unitSumSplineDensity n ((-Real.sqrt (n : ℝ) / 2) * y + (n : ℝ) / 2)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact diagonalPotential_eq_affine_log n hn hy
  have h := heq.iteratedDeriv_eq k
  rw [iteratedDeriv_const_sub hk, iteratedDeriv_neg,
    iteratedDeriv_affine_real (fun t => Real.log (Spline.unitSumSplineDensity n t))
      (-Real.sqrt (n : ℝ) / 2) ((n : ℝ) / 2) k] at h
  dsimp only at h
  have harg : (-Real.sqrt (n : ℝ) / 2) * x + (n : ℝ) / 2 =
      ((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2 := by ring
  rw [harg] at h
  simpa only [neg_mul] using h

theorem sumToDiagonal_mem_support (n : ℕ) (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (n : ℝ)) :
    sumToDiagonal n t ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  unfold sumToDiagonal
  constructor
  · apply (lt_div_iff₀ hs).mpr
    nlinarith [ht.2]
  · apply (div_lt_iff₀ hs).mpr
    nlinarith [ht.1]

theorem sumToDiagonal_inverse_coordinate (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ((n : ℝ) - Real.sqrt (n : ℝ) * sumToDiagonal n t) / 2 = t := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  unfold sumToDiagonal
  field_simp
  ring

theorem diagonalPotential_second_sumToDiagonal (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (n : ℝ)) :
    deriv (deriv (Spline.diagonalSplinePotential n)) (sumToDiagonal n t) =
      -(n : ℝ) / 4 * deriv (deriv (fun t => Real.log (Spline.unitSumSplineDensity n t))) t := by
  have h := diagonalPotential_iteratedDeriv n hn 2 (by norm_num)
    (sumToDiagonal_mem_support n (by omega) ht)
  rw [sumToDiagonal_inverse_coordinate n (by omega), div_pow, neg_sq,
    Real.sq_sqrt (Nat.cast_nonneg n)] at h
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
  rw [h]
  ring

theorem diagonalPotential_third_sumToDiagonal (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (n : ℝ)) :
    deriv (deriv (deriv (Spline.diagonalSplinePotential n))) (sumToDiagonal n t) =
      (Real.sqrt (n : ℝ) / 2) ^ 3 * logThirdUnitSum n t := by
  have h := diagonalPotential_iteratedDeriv n hn 3 (by norm_num)
    (sumToDiagonal_mem_support n (by omega) ht)
  rw [sumToDiagonal_inverse_coordinate n (by omega)] at h
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
  change _ = _ * logThirdUnitSum n t at h
  rw [h]
  ring

end
end ENT.Small
