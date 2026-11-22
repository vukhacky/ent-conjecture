module

public import ENT.Spline.DensityProperties
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp

/-! Exact truncated-power formula for the coordinate-square convolution
kernel. The integral is over continuous uniform[0,1], with all polynomial
identities proved in Lean. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ENT.Small
noncomputable section
open Spline

def quadraticPowerPrimitive (m : ℕ) (c u : ℝ) : ℝ :=
  c ^ 2 * (positivePower (m + 1) u / (m + 1 : ℕ)) +
    4 * c * (positivePower (m + 2) u / (m + 2 : ℕ)) +
    4 * (positivePower (m + 3) u / (m + 3 : ℕ))

theorem positivePower_succ_mul (m : ℕ) (hm : 0 < m) (u : ℝ) :
    positivePower (m + 1) u = u * positivePower m u := by
  by_cases hu : 0 ≤ u
  · simp only [positivePower, max_eq_right hu, pow_succ]
    ring
  · simp [positivePower, max_eq_left (le_of_not_ge hu), zero_pow (by omega : m ≠ 0)]

theorem quadraticPowerPrimitive_hasDerivAt (m : ℕ) (hm : 0 < m) (c u : ℝ) :
    HasDerivAt (quadraticPowerPrimitive m c) ((c + 2 * u) ^ 2 * positivePower m u) u := by
  have h1 : HasDerivAt (fun x => positivePower (m + 1) x / (m + 1 : ℕ))
      (positivePower m u) u := by
    convert (positivePower_hasDerivAt (m + 1) (by omega) u).div_const (m + 1 : ℕ) using 1
    simp only [Nat.add_sub_cancel]
    field_simp
  have h2 : HasDerivAt (fun x => positivePower (m + 2) x / (m + 2 : ℕ))
      (positivePower (m + 1) u) u := by
    convert (positivePower_hasDerivAt (m + 2) (by omega) u).div_const (m + 2 : ℕ) using 1
    rw [show m + 2 - 1 = m + 1 by omega]
    field_simp
  have h3 : HasDerivAt (fun x => positivePower (m + 3) x / (m + 3 : ℕ))
      (positivePower (m + 2) u) u := by
    convert (positivePower_hasDerivAt (m + 3) (by omega) u).div_const (m + 3 : ℕ) using 1
    rw [show m + 3 - 1 = m + 2 by omega]
    field_simp
  convert ((h1.const_mul (c ^ 2)).add (h2.const_mul (4 * c))).add (h3.const_mul 4) using 1
  · rfl
  · rw [show m + 2 = (m + 1) + 1 by omega,
      positivePower_succ_mul (m + 1) (by omega), positivePower_succ_mul m hm]
    ring

theorem integral_coordinate_square_positivePower (m : ℕ) (hm : 0 < m) (y : ℝ) :
    (∫ x in (0 : ℝ)..1, (1 - 2 * x) ^ 2 * positivePower m (y - x)) =
      quadraticPowerPrimitive m (1 - 2 * y) y -
        quadraticPowerPrimitive m (1 - 2 * y) (y - 1) := by
  have hd (x : ℝ) : HasDerivAt
      (fun x => -quadraticPowerPrimitive m (1 - 2 * y) (y - x))
      ((1 - 2 * x) ^ 2 * positivePower m (y - x)) x := by
    have h := ((quadraticPowerPrimitive_hasDerivAt m hm (1 - 2 * y) (y - x)).comp x
      ((hasDerivAt_const x y).sub (hasDerivAt_id x))).neg
    convert h using 1 <;> first | rfl | ring
  have hc : Continuous (fun x : ℝ => (1 - 2 * x) ^ 2 * positivePower m (y - x)) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).pow 2 |>.mul
      ((continuous_positivePower m).comp (continuous_const.sub continuous_id))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable 0 1)]
  simp only [sub_zero]
  ring

def coordinateSquareKernel (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 - 2 * x) ^ 2 * unitSumSplineDensity (n - 1) (t - x)

def coordinateSquareKernelFormula (n : ℕ) (t : ℝ) : ℝ :=
  (Nat.factorial (n - 2) : ℝ)⁻¹ *
    ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * ((n - 1).choose j : ℝ) *
      (quadraticPowerPrimitive (n - 2) (1 - 2 * (t - j)) (t - j) -
        quadraticPowerPrimitive (n - 2) (1 - 2 * (t - j)) (t - j - 1))

theorem coordinateSquareKernel_eq_formula (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    coordinateSquareKernel n t = coordinateSquareKernelFormula n t := by
  have hn1 : n - 1 + 1 = n := by omega
  have hn2 : n - 1 - 1 = n - 2 := by omega
  unfold coordinateSquareKernel unitSumSplineDensity unnormalizedSpline
  simp only [hn1, hn2]
  have heq : (fun x : ℝ => (1 - 2 * x) ^ 2 *
      ((Nat.factorial (n - 2) : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
        (-1 : ℝ) ^ j * ((n - 1).choose j : ℝ) * positivePower (n - 2) (t - x - j))) =
      (fun x => (Nat.factorial (n - 2) : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
        ((-1 : ℝ) ^ j * ((n - 1).choose j : ℝ)) *
          ((1 - 2 * x) ^ 2 * positivePower (n - 2) (t - j - x))) := by
    funext x
    rw [← mul_assoc, mul_comm ((1 - 2 * x) ^ 2), mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show t - x - (j : ℝ) = t - j - x by ring]
    ring
  rw [heq, intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · unfold coordinateSquareKernelFormula
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul, integral_coordinate_square_positivePower _ (by omega)]
  · intro j _
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (((continuous_const.sub (continuous_const.mul continuous_id)).pow 2).mul
        ((continuous_positivePower (n - 2)).comp (continuous_const.sub continuous_id)))

def varianceKernel (n : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ) * coordinateSquareKernel n t -
    ((n : ℝ) - 2 * t) ^ 2 / n * unitSumSplineDensity n t) / ((n : ℝ) - 1)

end
end ENT.Small
