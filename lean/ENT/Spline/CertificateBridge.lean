module

public import ENT.Spline.DensityLaw
public import ENT.Spline.PositiveInterior
public import ENT.Certificate.CompleteChecker
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Generic bridge from every reflected cell certificate in a dimension to
the global curvature of the genuine diagonal projection density. The
ceiling-based cell cover includes the center of even-dimensional splines. -/

@[expose] public section

set_option autoImplicit false

open Set
open ENT.Certificate

namespace ENT.Spline

noncomputable section

def CellwiseCurvature (n : ℕ) : Prop :=
  ∀ k : ℕ, 2 * k < n → ∀ s : ℝ, 0 ≤ s →
    s ≤ (if 2 * k + 1 = n then (1 / 2 : ℝ) else 1) → 0 ≤ targetPolynomial n k s

theorem reflected_cell_cover (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < Real.sqrt (n : ℝ)) :
    ∃ k : ℕ, 2 * k < n ∧ 0 ≤ standardizedCellCoordinate n k x ∧
      standardizedCellCoordinate n k x ≤ if 2 * k + 1 = n then (1 / 2 : ℝ) else 1 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hr2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  let t : ℝ := ((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2
  have ht0 : 0 < t := by
    have hp := mul_lt_mul_of_pos_left hx1 hr
    dsimp [t]
    nlinarith
  have htn : t ≤ (n : ℝ) / 2 := by
    dsimp [t]
    nlinarith [mul_nonneg hr.le hx0]
  have hcpos : 1 ≤ Nat.ceil t := Nat.one_le_ceil_iff.mpr ht0
  have hcne : Nat.ceil t ≠ 0 := by omega
  have hb := (Nat.ceil_eq_iff hcne).mp (rfl : Nat.ceil t = Nat.ceil t)
  let k : ℕ := Nat.ceil t - 1
  have hkt : (k : ℝ) < t := hb.1
  have hceil : Nat.ceil t = k + 1 := by dsimp [k]; omega
  have htk : t ≤ (k : ℝ) + 1 := by
    simpa only [hceil, Nat.cast_add, Nat.cast_one] using hb.2
  have hk : 2 * k < n := by
    have hreal : (2 : ℝ) * (k : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast hreal
  refine ⟨k, hk, ?_, ?_⟩
  · change 0 ≤ t - (k : ℝ)
    linarith
  · change t - (k : ℝ) ≤ if 2 * k + 1 = n then (1 / 2 : ℝ) else 1
    split_ifs with hcenter
    · have hc : (2 : ℝ) * (k : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hcenter
      linarith
    · linarith

theorem cellwiseCurvature_of_checked_data (n : ℕ)
    (hdata : ∀ k : ℕ, 2 * k < n →
      ∃ c : CellData, c.n = n ∧ c.k = k ∧ checkCell c = true) : CellwiseCurvature n := by
  intro k hk s hs0 hs1
  obtain ⟨c, hcn, hck, hc⟩ := hdata k hk
  rcases checkCell_sound c hc with ⟨_, _, _, hhalf, _, _, htarget⟩
  simp only [hcn, hck] at hhalf
  have hw : width c = if 2 * k + 1 = n then (1 / 2 : ℝ) else 1 := by
    by_cases hf : c.halfCell = true
    · simp [width, hf, hhalf.mp hf]
    · have hcenter : ¬2 * k + 1 = n := fun h => hf (hhalf.mpr h)
      simp [width, hf, hcenter]
  have hs : s ≤ width c := by rw [hw]; exact hs1
  simpa only [hcn, hck] using htarget s hs0 hs

theorem unnormalizedSpline_standardized_pos (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    0 < unnormalizedSpline n (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2) := by
  have hq := diagonalSplineDensity_pos n hn x hx
  rw [diagonalSplineDensity_eq] at hq
  exact (mul_pos_iff_of_pos_left (normalizationConstant_pos n (by omega))).mp hq

theorem diagonalSpline_curvature_of_cellwise (n : ℕ) (hn : 5 ≤ n)
    (hcert : CellwiseCurvature n) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < Real.sqrt (n : ℝ)) :
    (7 / (n : ℝ)) * x ≤ deriv (deriv (deriv (diagonalSplinePotential n))) x := by
  obtain ⟨k, hk, hs0, hs1⟩ := reflected_cell_cover n (by omega) x hx0 hx1
  have hs1' : standardizedCellCoordinate n k x ≤ 1 := by
    split_ifs at hs1 <;> linarith
  have hr : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega : 0 < n))
  have hglobal := unnormalizedSpline_standardized_pos n (by omega) x
    ⟨by linarith, hx1⟩
  have hcoord : (k : ℝ) + standardizedCellCoordinate n k x =
      ((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2 := by
    unfold standardizedCellCoordinate
    ring
  have hp : 0 < splinePiece n k (standardizedCellCoordinate n k x) := by
    rw [← hcoord, unnormalizedSpline_eq_piece n k (by omega) (by omega) _ hs0 hs1'] at hglobal
    exact hglobal
  rw [third_deriv_diagonalSplinePotential_eq n (by omega) x (ne_of_gt hglobal),
    third_deriv_unnormalizedPotential_eq_cell n k hn (by omega) x hs0 hs1' (ne_of_gt hp)]
  exact standardizedCellPotential_curvature_lower n k x (by omega) hp
    (hcert k hk _ hs0 hs1)

theorem diagonalFiniteEntropyDensity_curvature_of_cellwise (n : ℕ) (hn : 5 ≤ n)
    (hcert : CellwiseCurvature n) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < Real.sqrt (n : ℝ)) :
    (7 / (n : ℝ)) * x ≤ deriv (deriv (deriv
      (fun y => -Real.log ((diagonalFiniteEntropyDensity n (by omega)).density y)))) x :=
  diagonalSpline_curvature_of_cellwise n hn hcert x hx0 hx1

end
end ENT.Spline
