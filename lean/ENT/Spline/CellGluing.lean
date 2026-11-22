module

public import ENT.Spline.Global
public import ENT.Certificate.StandardizedCurvature
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Matching higher derivatives at knots via equal functions on a closed
interval with unique derivatives. No open-cell-only argument is used. -/

@[expose] public section

set_option autoImplicit false

open Set
open scoped ContDiff
open ENT.Certificate

namespace ENT.Spline

noncomputable section

def unnormalizedPotential (n : ℕ) (x : ℝ) : ℝ :=
  -Real.log (unnormalizedSpline n (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2))

def cellLeft (n k : ℕ) : ℝ :=
  ((n : ℝ) - 2 * (k : ℝ) - 2) / Real.sqrt (n : ℝ)

def cellRight (n k : ℕ) : ℝ :=
  ((n : ℝ) - 2 * (k : ℝ)) / Real.sqrt (n : ℝ)

theorem cellLeft_lt_right (n k : ℕ) (hn : 0 < n) : cellLeft n k < cellRight n k := by
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  unfold cellLeft cellRight
  exact (div_lt_div_iff_of_pos_right hr).mpr (by linarith)

theorem mem_cell_iff (n k : ℕ) (hn : 0 < n) (x : ℝ) :
    x ∈ Icc (cellLeft n k) (cellRight n k) ↔
      0 ≤ standardizedCellCoordinate n k x ∧ standardizedCellCoordinate n k x ≤ 1 := by
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  simp only [mem_Icc, cellLeft, cellRight, div_le_iff₀ hr, le_div_iff₀ hr,
    standardizedCellCoordinate]
  constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> nlinarith

theorem standardizedCellPotential_eq (n k : ℕ) (x : ℝ) :
    standardizedCellPotential n k x =
      -Real.log (splinePiece n k (standardizedCellCoordinate n k x)) := by
  unfold standardizedCellPotential affineLogPotential
  rw [standardizedCellCoordinate_affine, splinePolynomial_eval]

theorem unnormalizedPotential_eqOn_cell (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n) :
    EqOn (unnormalizedPotential n) (standardizedCellPotential n k)
      (Icc (cellLeft n k) (cellRight n k)) := by
  intro x hx
  obtain ⟨hs0, hs1⟩ := (mem_cell_iff n k (by omega) x).mp hx
  have hcoord : (k : ℝ) + standardizedCellCoordinate n k x =
      ((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2 := by
    unfold standardizedCellCoordinate
    ring
  rw [standardizedCellPotential_eq, unnormalizedPotential, ← hcoord,
    unnormalizedSpline_eq_piece n k hn hk _ hs0 hs1]

theorem contDiff_splinePiece (r n k : ℕ) : ContDiff ℝ r (splinePiece n k) := by
  unfold splinePiece
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul
    (((contDiff_const.add contDiff_id).sub contDiff_const).pow (n - 1))

theorem contDiffAt_standardizedCellPotential (r n k : ℕ) (x : ℝ)
    (hp : splinePiece n k (standardizedCellCoordinate n k x) ≠ 0) :
    ContDiffAt ℝ r (standardizedCellPotential n k) x := by
  have hfun : standardizedCellPotential n k = fun y =>
      -Real.log (splinePiece n k (standardizedCellCoordinate n k y)) := by
    funext y
    exact standardizedCellPotential_eq n k y
  rw [hfun]
  have hc : ContDiff ℝ r (standardizedCellCoordinate n k) :=
    (((contDiff_const.sub (contDiff_const.mul contDiff_id)).div_const 2).sub contDiff_const)
  exact (((contDiff_splinePiece r n k).comp hc).contDiffAt.log hp).neg

theorem contDiffAt_unnormalizedPotential (r n : ℕ) (hrn : r < n - 1)
    (x : ℝ)
    (hp : unnormalizedSpline n (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2) ≠ 0) :
    ContDiffAt ℝ r (unnormalizedPotential n) x := by
  have hc : ContDiff ℝ r (fun y : ℝ => ((n : ℝ) - Real.sqrt (n : ℝ) * y) / 2) :=
    (contDiff_const.sub (contDiff_const.mul contDiff_id)).div_const 2
  exact (((contDiff_unnormalizedSpline r n hrn).comp hc).contDiffAt.log hp).neg

theorem iteratedDeriv_eq_of_eqOn_Icc (r : ℕ) (f g : ℝ → ℝ) (a b x : ℝ)
    (hab : a < b) (hx : x ∈ Icc a b) (hf : ContDiffAt ℝ r f x)
    (hg : ContDiffAt ℝ r g x) (heq : EqOn f g (Icc a b)) :
    iteratedDeriv r f x = iteratedDeriv r g x := by
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hf hx,
    ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hg hx]
  exact iteratedDerivWithin_congr heq hx

theorem third_deriv_unnormalizedPotential_eq_cell (n k : ℕ) (hn : 5 ≤ n)
    (hk : k ≤ n) (x : ℝ)
    (hs0 : 0 ≤ standardizedCellCoordinate n k x)
    (hs1 : standardizedCellCoordinate n k x ≤ 1)
    (hp : splinePiece n k (standardizedCellCoordinate n k x) ≠ 0) :
    deriv (deriv (deriv (unnormalizedPotential n))) x =
      deriv (deriv (deriv (standardizedCellPotential n k))) x := by
  have hx := (mem_cell_iff n k (by omega) x).mpr ⟨hs0, hs1⟩
  have hcoord : (k : ℝ) + standardizedCellCoordinate n k x =
      ((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2 := by
    unfold standardizedCellCoordinate
    ring
  have hpglobal : unnormalizedSpline n
      (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2) ≠ 0 := by
    rw [← hcoord, unnormalizedSpline_eq_piece n k (by omega) hk _ hs0 hs1]
    exact hp
  have h := iteratedDeriv_eq_of_eqOn_Icc 3 (unnormalizedPotential n)
    (standardizedCellPotential n k) (cellLeft n k) (cellRight n k) x
    (cellLeft_lt_right n k (by omega)) hx
    (contDiffAt_unnormalizedPotential 3 n (by omega) x hpglobal)
    (contDiffAt_standardizedCellPotential 3 n k x hp)
    (unnormalizedPotential_eqOn_cell n k (by omega) hk)
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h

end
end ENT.Spline
