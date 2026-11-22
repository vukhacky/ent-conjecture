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

def n7k3P : Polynomial ℝ := 302 + 240 * X - 150 * X ^ 2 - 160 * X ^ 3 + 30 * X ^ 4 + 60 * X ^ 5 - 20 * X ^ 6
def n7k3R : Polynomial ℝ := 283744832 + 48153056 * X + 16031151360 * X ^ 2 - 53667374880 * X ^ 3 + 12015477600 * X ^ 4 + 79768130400 * X ^ 5 - 37983412320 * X ^ 6 - 52583590080 * X ^ 7 + 39799922400 * X ^ 8 + 3814294400 * X ^ 9 - 11947566400 * X ^ 10 + 4196707200 * X ^ 11 + 981052800 * X ^ 12 - 1349107200 * X ^ 13 + 219744000 * X ^ 14 + 116928000 * X ^ 15 - 11424000 * X ^ 16 - 24192000 * X ^ 17 + 8512000 * X ^ 18 - 896000 * X ^ 19
def n7k3Q : Polynomial ℝ := 148764010479616 + 12623034712064 * X + 2101235071057920 * X ^ 2 - 3517145080135680 * X ^ 3 + 393723169996800 * X ^ 4 + 1306921048473600 * X ^ 5 - 311160113725440 * X ^ 6 - 215382384967680 * X ^ 7 + 81510241075200 * X ^ 8 + 3905837465600 * X ^ 9 - 6117153996800 * X ^ 10 + 1074357043200 * X ^ 11 + 125574758400 * X ^ 12 - 86342860800 * X ^ 13 + 7031808000 * X ^ 14 + 1870848000 * X ^ 15 - 91392000 * X ^ 16 - 96768000 * X ^ 17 + 17024000 * X ^ 18 - 896000 * X ^ 19
def n7k3B : Fin 20 → ℝ := ![148764010479616, 2839139233824768, 27767095487889408, 178287501593542656, 816797072495738880, 2782449607377420288, 7235084185402343424, 14625306944197361664, 23273970247568130048, 29382674510802780160, 29522831371803721728, 23576393722079084544, 14867899978087317504, 7310485872937648128, 2743229219282657280, 758563734819373056, 145645671999141888, 17335665630517248, 963092535028736, 0]

theorem n7k3_spline : splinePolynomial 7 3 = n7k3P := by
  norm_num [splinePolynomial, Finset.sum_range_succ, Nat.choose, Polynomial.C_ofNat, Polynomial.C_eq_natCast, n7k3P]
  <;> ring

theorem n7k3_curvature : curvaturePolynomial 7 3 = n7k3R := by
  unfold curvaturePolynomial
  rw [n7k3_spline]
  norm_num [logarithmicNumeratorPolynomial, n7k3P, n7k3R,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  <;> ring

theorem n7k3_bernstein_identity (x : ℝ) :
    n7k3Q.eval x = bernsteinEval 19 n7k3B x := by
  norm_num [bernsteinEval, Fin.sum_univ_succ, n7k3B, n7k3Q]
  <;> ring

theorem n7k3_bernstein_nonneg (j : Fin 20) : 0 ≤ n7k3B j := by
  fin_cases j <;> norm_num [n7k3B]

theorem n7k3_unit_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ n7k3Q.eval x :=
  bernstein_identity_nonneg 19 n7k3B (fun x => n7k3Q.eval x)
    n7k3_bernstein_identity n7k3_bernstein_nonneg x hx0 hx1

theorem n7k3_half_identity (x : ℝ) :
    n7k3Q.eval x = 524288 * n7k3R.eval (x / 2) := by
  norm_num [n7k3Q, n7k3R] <;> ring

theorem n7k3_raw_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    0 ≤ n7k3R.eval s :=
  halfCell_nonneg (fun x => n7k3R.eval x) (fun x => n7k3Q.eval x)
    524288 (by norm_num) n7k3_half_identity
    n7k3_unit_nonneg s hs0 hs1

theorem n7k3_target_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    0 ≤ targetPolynomial 7 3 s := by
  rw [← curvaturePolynomial_eval, n7k3_curvature]
  exact n7k3_raw_nonneg s hs0 hs1

def n7k3Data : CellData where
  n := 7
  k := 3
  degreeBound := 19
  halfCell := true
  pCoeffs := [302, 240, -150, -160, 30, 60, -20]
  rCoeffs := [283744832, 48153056, 16031151360, -53667374880, 12015477600, 79768130400, -37983412320, -52583590080, 39799922400, 3814294400, -11947566400, 4196707200, 981052800, -1349107200, 219744000, 116928000, -11424000, -24192000, 8512000, -896000]
  transformedCoeffs := [148764010479616, 12623034712064, 2101235071057920, -3517145080135680, 393723169996800, 1306921048473600, -311160113725440, -215382384967680, 81510241075200, 3905837465600, -6117153996800, 1074357043200, 125574758400, -86342860800, 7031808000, 1870848000, -91392000, -96768000, 17024000, -896000]
  bernsteinNumerators := [148764010479616, 2839139233824768, 27767095487889408, 178287501593542656, 816797072495738880, 2782449607377420288, 7235084185402343424, 14625306944197361664, 23273970247568130048, 29382674510802780160, 29522831371803721728, 23576393722079084544, 14867899978087317504, 7310485872937648128, 2743229219282657280, 758563734819373056, 145645671999141888, 17335665630517248, 963092535028736, 0]

theorem n7k3_pCoeffs (s : ℝ) :
    ENT.Certificate.eval n7k3Data.pCoeffs s = splinePiece 7 3 s := by
  rw [← splinePolynomial_eval, n7k3_spline]
  norm_num [ENT.Certificate.eval, n7k3Data, n7k3P] <;> ring

theorem n7k3_rCoeffs (s : ℝ) :
    ENT.Certificate.eval n7k3Data.rCoeffs s = targetPolynomial 7 3 s := by
  rw [← curvaturePolynomial_eval, n7k3_curvature]
  norm_num [ENT.Certificate.eval, n7k3Data, n7k3R] <;> ring

theorem n7k3_conclusion : CellConclusion n7k3Data := by
  refine ⟨by norm_num [n7k3Data], by norm_num [n7k3Data],
    by norm_num [n7k3Data], by norm_num [n7k3Data],
    n7k3_pCoeffs, n7k3_rCoeffs, ?_⟩
  intro s hs0 hs1
  exact n7k3_target_nonneg s hs0 (by simpa [width, n7k3Data] using hs1)

end
end ENT.Pilot
