module

public import ENT.Certificate.Bernstein
public import ENT.Certificate.PolynomialSemantics
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Explicit generated data; every identity and sign below is proved in Lean. -/
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

open Polynomial
open ENT.Certificate

namespace ENT.Pilot
noncomputable section

def n7k1P : Polynomial ℝ := 1 + 6 * X + 15 * X ^ 2 + 20 * X ^ 3 + 15 * X ^ 4 + 6 * X ^ 5 - 6 * X ^ 6
def n7k1R : Polynomial ℝ := 3836 + 56812 * X + 391356 * X ^ 2 + 1373316 * X ^ 3 + 2692032 * X ^ 4 + 3734892 * X ^ 5 + 6860196 * X ^ 6 + 15833496 * X ^ 7 + 25937604 * X ^ 8 + 20085184 * X ^ 9 - 5450872 * X ^ 10 - 21261744 * X ^ 11 - 11069856 * X ^ 12 + 1933344 * X ^ 13 + 2854656 * X ^ 14 - 1221696 * X ^ 15 - 368928 * X ^ 16 - 72576 * X ^ 17 + 133056 * X ^ 18 - 24192 * X ^ 19
def n7k1Q : Polynomial ℝ := 3836 + 56812 * X + 391356 * X ^ 2 + 1373316 * X ^ 3 + 2692032 * X ^ 4 + 3734892 * X ^ 5 + 6860196 * X ^ 6 + 15833496 * X ^ 7 + 25937604 * X ^ 8 + 20085184 * X ^ 9 - 5450872 * X ^ 10 - 21261744 * X ^ 11 - 11069856 * X ^ 12 + 1933344 * X ^ 13 + 2854656 * X ^ 14 - 1221696 * X ^ 15 - 368928 * X ^ 16 - 72576 * X ^ 17 + 133056 * X ^ 18 - 24192 * X ^ 19
def n7k1B : Fin 20 → ℝ := ![3836, 129696, 2069928, 20435688, 139116432, 693485100, 2633139852, 7838858160, 18725142996, 36584172128, 59302413240, 80283331044, 90368936616, 83163724140, 60831512028, 34032219480, 13830923736, 3785426568, 610967448, 42419916]

theorem n7k1_spline : splinePolynomial 7 1 = n7k1P := by
  norm_num [splinePolynomial, Finset.sum_range_succ, Nat.choose, Polynomial.C_ofNat, Polynomial.C_eq_natCast, n7k1P]
  <;> ring

theorem n7k1_curvature : curvaturePolynomial 7 1 = n7k1R := by
  unfold curvaturePolynomial
  rw [n7k1_spline]
  norm_num [logarithmicNumeratorPolynomial, n7k1P, n7k1R,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  <;> ring

theorem n7k1_bernstein_identity (x : ℝ) :
    n7k1Q.eval x = bernsteinEval 19 n7k1B x := by
  norm_num [bernsteinEval, Fin.sum_univ_succ, n7k1B, n7k1Q]
  <;> ring

theorem n7k1_bernstein_nonneg (j : Fin 20) : 0 ≤ n7k1B j := by
  fin_cases j <;> norm_num [n7k1B]

theorem n7k1_unit_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ n7k1Q.eval x :=
  bernstein_identity_nonneg 19 n7k1B (fun x => n7k1Q.eval x)
    n7k1_bernstein_identity n7k1_bernstein_nonneg x hx0 hx1

theorem n7k1_raw_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ n7k1R.eval s := by
  exact n7k1_unit_nonneg s hs0 hs1

theorem n7k1_target_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ targetPolynomial 7 1 s := by
  rw [← curvaturePolynomial_eval, n7k1_curvature]
  exact n7k1_raw_nonneg s hs0 hs1

def n7k1Data : CellData where
  n := 7
  k := 1
  degreeBound := 19
  halfCell := false
  pCoeffs := [1, 6, 15, 20, 15, 6, -6]
  rCoeffs := [3836, 56812, 391356, 1373316, 2692032, 3734892, 6860196, 15833496, 25937604, 20085184, -5450872, -21261744, -11069856, 1933344, 2854656, -1221696, -368928, -72576, 133056, -24192]
  transformedCoeffs := [3836, 56812, 391356, 1373316, 2692032, 3734892, 6860196, 15833496, 25937604, 20085184, -5450872, -21261744, -11069856, 1933344, 2854656, -1221696, -368928, -72576, 133056, -24192]
  bernsteinNumerators := [3836, 129696, 2069928, 20435688, 139116432, 693485100, 2633139852, 7838858160, 18725142996, 36584172128, 59302413240, 80283331044, 90368936616, 83163724140, 60831512028, 34032219480, 13830923736, 3785426568, 610967448, 42419916]

theorem n7k1_pCoeffs (s : ℝ) :
    ENT.Certificate.eval n7k1Data.pCoeffs s = splinePiece 7 1 s := by
  rw [← splinePolynomial_eval, n7k1_spline]
  norm_num [ENT.Certificate.eval, n7k1Data, n7k1P] <;> ring

theorem n7k1_rCoeffs (s : ℝ) :
    ENT.Certificate.eval n7k1Data.rCoeffs s = targetPolynomial 7 1 s := by
  rw [← curvaturePolynomial_eval, n7k1_curvature]
  norm_num [ENT.Certificate.eval, n7k1Data, n7k1R] <;> ring

theorem n7k1_conclusion : CellConclusion n7k1Data := by
  refine ⟨by norm_num [n7k1Data], by norm_num [n7k1Data],
    by norm_num [n7k1Data], by norm_num [n7k1Data],
    n7k1_pCoeffs, n7k1_rCoeffs, ?_⟩
  intro s hs0 hs1
  exact n7k1_target_nonneg s hs0 (by simpa [width, n7k1Data] using hs1)

end
end ENT.Pilot
