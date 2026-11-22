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

def n7k0P : Polynomial ℝ := X ^ 6
def n7k0R : Polynomial ℝ := 4116 * X ^ 15 - 392 * X ^ 18 + 112 * X ^ 19
def n7k0Q : Polynomial ℝ := 4116 * X ^ 15 - 392 * X ^ 18 + 112 * X ^ 19
def n7k0B : Fin 20 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4116, 16464, 24696, 16072, 3836]

theorem n7k0_spline : splinePolynomial 7 0 = n7k0P := by
  norm_num [splinePolynomial, Finset.sum_range_succ, Nat.choose, Polynomial.C_ofNat, Polynomial.C_eq_natCast, n7k0P]
  <;> ring

theorem n7k0_curvature : curvaturePolynomial 7 0 = n7k0R := by
  unfold curvaturePolynomial
  rw [n7k0_spline]
  norm_num [logarithmicNumeratorPolynomial, n7k0P, n7k0R,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  <;> ring

theorem n7k0_bernstein_identity (x : ℝ) :
    n7k0Q.eval x = bernsteinEval 19 n7k0B x := by
  norm_num [bernsteinEval, Fin.sum_univ_succ, n7k0B, n7k0Q]
  <;> ring

theorem n7k0_bernstein_nonneg (j : Fin 20) : 0 ≤ n7k0B j := by
  fin_cases j <;> norm_num [n7k0B]

theorem n7k0_unit_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ n7k0Q.eval x :=
  bernstein_identity_nonneg 19 n7k0B (fun x => n7k0Q.eval x)
    n7k0_bernstein_identity n7k0_bernstein_nonneg x hx0 hx1

theorem n7k0_raw_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ n7k0R.eval s := by
  exact n7k0_unit_nonneg s hs0 hs1

theorem n7k0_target_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ targetPolynomial 7 0 s := by
  rw [← curvaturePolynomial_eval, n7k0_curvature]
  exact n7k0_raw_nonneg s hs0 hs1

def n7k0Data : CellData where
  n := 7
  k := 0
  degreeBound := 19
  halfCell := false
  pCoeffs := [0, 0, 0, 0, 0, 0, 1]
  rCoeffs := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4116, 0, 0, -392, 112]
  transformedCoeffs := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4116, 0, 0, -392, 112]
  bernsteinNumerators := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4116, 16464, 24696, 16072, 3836]

theorem n7k0_pCoeffs (s : ℝ) :
    ENT.Certificate.eval n7k0Data.pCoeffs s = splinePiece 7 0 s := by
  rw [← splinePolynomial_eval, n7k0_spline]
  norm_num [ENT.Certificate.eval, n7k0Data, n7k0P] <;> ring

theorem n7k0_rCoeffs (s : ℝ) :
    ENT.Certificate.eval n7k0Data.rCoeffs s = targetPolynomial 7 0 s := by
  rw [← curvaturePolynomial_eval, n7k0_curvature]
  norm_num [ENT.Certificate.eval, n7k0Data, n7k0R] <;> ring

theorem n7k0_conclusion : CellConclusion n7k0Data := by
  refine ⟨by norm_num [n7k0Data], by norm_num [n7k0Data],
    by norm_num [n7k0Data], by norm_num [n7k0Data],
    n7k0_pCoeffs, n7k0_rCoeffs, ?_⟩
  intro s hs0 hs1
  exact n7k0_target_nonneg s hs0 (by simpa [width, n7k0Data] using hs1)

end
end ENT.Pilot
