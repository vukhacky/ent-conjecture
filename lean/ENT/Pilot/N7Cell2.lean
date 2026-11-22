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

def n7k2P : Polynomial ℝ := 57 + 150 * X + 135 * X ^ 2 + 20 * X ^ 3 - 45 * X ^ 4 - 30 * X ^ 5 + 15 * X ^ 6
def n7k2R : Polynomial ℝ := 42419916 + 195010956 * X + 41818140 * X ^ 2 + 956512620 * X ^ 3 + 2663457300 * X ^ 4 - 243904500 * X ^ 5 - 5495445060 * X ^ 6 - 3354962940 * X ^ 7 + 3742760700 * X ^ 8 + 3197714100 * X ^ 9 - 992809300 * X ^ 10 - 838082700 * X ^ 11 + 358677900 * X ^ 12 + 125111700 * X ^ 13 - 123511500 * X ^ 14 - 3496500 * X ^ 15 + 10395000 * X ^ 16 + 4536000 * X ^ 17 - 2835000 * X ^ 18 + 378000 * X ^ 19
def n7k2Q : Polynomial ℝ := 42419916 + 195010956 * X + 41818140 * X ^ 2 + 956512620 * X ^ 3 + 2663457300 * X ^ 4 - 243904500 * X ^ 5 - 5495445060 * X ^ 6 - 3354962940 * X ^ 7 + 3742760700 * X ^ 8 + 3197714100 * X ^ 9 - 992809300 * X ^ 10 - 838082700 * X ^ 11 + 358677900 * X ^ 12 + 125111700 * X ^ 13 - 123511500 * X ^ 14 - 3496500 * X ^ 15 + 10395000 * X ^ 16 + 4536000 * X ^ 17 - 2835000 * X ^ 18 + 378000 * X ^ 19
def n7k2B : Fin 20 → ℝ := ![42419916, 1000989360, 10805820984, 72608995872, 347203460772, 1272918113208, 3727718180760, 8872143746592, 17189475646896, 26930445768576, 33771011120168, 33491625254640, 25890969665232, 15312852967776, 6752339639136, 2139734777376, 462389790240, 63684762624, 5342998752, 283744832]

theorem n7k2_spline : splinePolynomial 7 2 = n7k2P := by
  norm_num [splinePolynomial, Finset.sum_range_succ, Nat.choose, Polynomial.C_ofNat, Polynomial.C_eq_natCast, n7k2P]
  <;> ring

theorem n7k2_curvature : curvaturePolynomial 7 2 = n7k2R := by
  unfold curvaturePolynomial
  rw [n7k2_spline]
  norm_num [logarithmicNumeratorPolynomial, n7k2P, n7k2R,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  <;> ring

theorem n7k2_bernstein_identity (x : ℝ) :
    n7k2Q.eval x = bernsteinEval 19 n7k2B x := by
  norm_num [bernsteinEval, Fin.sum_univ_succ, n7k2B, n7k2Q]
  <;> ring

theorem n7k2_bernstein_nonneg (j : Fin 20) : 0 ≤ n7k2B j := by
  fin_cases j <;> norm_num [n7k2B]

theorem n7k2_unit_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ n7k2Q.eval x :=
  bernstein_identity_nonneg 19 n7k2B (fun x => n7k2Q.eval x)
    n7k2_bernstein_identity n7k2_bernstein_nonneg x hx0 hx1

theorem n7k2_raw_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ n7k2R.eval s := by
  exact n7k2_unit_nonneg s hs0 hs1

theorem n7k2_target_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ targetPolynomial 7 2 s := by
  rw [← curvaturePolynomial_eval, n7k2_curvature]
  exact n7k2_raw_nonneg s hs0 hs1

def n7k2Data : CellData where
  n := 7
  k := 2
  degreeBound := 19
  halfCell := false
  pCoeffs := [57, 150, 135, 20, -45, -30, 15]
  rCoeffs := [42419916, 195010956, 41818140, 956512620, 2663457300, -243904500, -5495445060, -3354962940, 3742760700, 3197714100, -992809300, -838082700, 358677900, 125111700, -123511500, -3496500, 10395000, 4536000, -2835000, 378000]
  transformedCoeffs := [42419916, 195010956, 41818140, 956512620, 2663457300, -243904500, -5495445060, -3354962940, 3742760700, 3197714100, -992809300, -838082700, 358677900, 125111700, -123511500, -3496500, 10395000, 4536000, -2835000, 378000]
  bernsteinNumerators := [42419916, 1000989360, 10805820984, 72608995872, 347203460772, 1272918113208, 3727718180760, 8872143746592, 17189475646896, 26930445768576, 33771011120168, 33491625254640, 25890969665232, 15312852967776, 6752339639136, 2139734777376, 462389790240, 63684762624, 5342998752, 283744832]

theorem n7k2_pCoeffs (s : ℝ) :
    ENT.Certificate.eval n7k2Data.pCoeffs s = splinePiece 7 2 s := by
  rw [← splinePolynomial_eval, n7k2_spline]
  norm_num [ENT.Certificate.eval, n7k2Data, n7k2P] <;> ring

theorem n7k2_rCoeffs (s : ℝ) :
    ENT.Certificate.eval n7k2Data.rCoeffs s = targetPolynomial 7 2 s := by
  rw [← curvaturePolynomial_eval, n7k2_curvature]
  norm_num [ENT.Certificate.eval, n7k2Data, n7k2R] <;> ring

theorem n7k2_conclusion : CellConclusion n7k2Data := by
  refine ⟨by norm_num [n7k2Data], by norm_num [n7k2Data],
    by norm_num [n7k2Data], by norm_num [n7k2Data],
    n7k2_pCoeffs, n7k2_rCoeffs, ?_⟩
  intro s hs0 hs1
  exact n7k2_target_nonneg s hs0 (by simpa [width, n7k2Data] using hs1)

end
end ENT.Pilot
