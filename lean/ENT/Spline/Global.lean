module

public import ENT.Spline.PositivePower
public import ENT.Certificate.Contract
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Global truncated-power spline and exact agreement with its polynomial pieces. -/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators ContDiff

namespace ENT.Spline

noncomputable section

def unnormalizedSpline (n : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ j * (n.choose j : ℝ) * positivePower (n - 1) (t - (j : ℝ))

def unitSumSplineDensity (n : ℕ) (t : ℝ) : ℝ :=
  (Nat.factorial (n - 1) : ℝ)⁻¹ * unnormalizedSpline n t

def diagonalSplineDensity (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) / 2 * unitSumSplineDensity n
    (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2)

def diagonalSplinePotential (n : ℕ) (x : ℝ) : ℝ :=
  -Real.log (diagonalSplineDensity n x)

theorem continuous_unnormalizedSpline (n : ℕ) : Continuous (unnormalizedSpline n) := by
  unfold unnormalizedSpline
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul
    ((continuous_positivePower (n - 1)).comp (continuous_id.sub continuous_const))

theorem contDiff_unnormalizedSpline (r n : ℕ) (hrn : r < n - 1) :
    ContDiff ℝ r (unnormalizedSpline n) := by
  unfold unnormalizedSpline
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul
    ((contDiff_positivePower r (n - 1) hrn).comp (contDiff_id.sub contDiff_const))

theorem unnormalizedSpline_eq_piece (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    unnormalizedSpline n ((k : ℝ) + s) = ENT.Certificate.splinePiece n k s := by
  unfold unnormalizedSpline ENT.Certificate.splinePiece
  have hsub : Finset.range (k + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (Nat.succ_le_succ hk)
  calc
    _ = ∑ j ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ j * (n.choose j : ℝ) *
          positivePower (n - 1) ((k : ℝ) + s - (j : ℝ)) := by
      symm
      apply Finset.sum_subset hsub
      intro j hj hnot
      have hjk : k + 1 ≤ j := by simpa only [Finset.mem_range, not_lt] using hnot
      have hjk' : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hjk
      have hneg : (k : ℝ) + s - (j : ℝ) ≤ 0 := by linarith
      simp [positivePower, max_eq_left hneg, zero_pow (by omega : n - 1 ≠ 0)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j ≤ k := by simp only [Finset.mem_range] at hj; omega
      have hjk' : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
      have hpos : 0 ≤ (k : ℝ) + s - (j : ℝ) := by linarith
      simp only [positivePower, max_eq_right hpos]

theorem contDiff_unitSumSplineDensity (r n : ℕ) (hrn : r < n - 1) :
    ContDiff ℝ r (unitSumSplineDensity n) :=
  contDiff_const.mul (contDiff_unnormalizedSpline r n hrn)

theorem contDiff_diagonalSplineDensity (r n : ℕ) (hrn : r < n - 1) :
    ContDiff ℝ r (diagonalSplineDensity n) := by
  unfold diagonalSplineDensity
  exact contDiff_const.mul
    ((contDiff_unitSumSplineDensity r n hrn).comp
      ((contDiff_const.sub (contDiff_const.mul contDiff_id)).div_const 2))

theorem contDiffAt_diagonalSplinePotential (r n : ℕ) (hrn : r < n - 1)
    (x : ℝ) (hp : diagonalSplineDensity n x ≠ 0) :
    ContDiffAt ℝ r (diagonalSplinePotential n) x :=
  ((contDiff_diagonalSplineDensity r n hrn).contDiffAt.log hp).neg

end
end ENT.Spline
