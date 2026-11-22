module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Algebraic implications in Pang’s logarithmic-curvature bounds (18), (44), and (51), at the threshold `n ≥ 150`. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Pang

noncomputable section

/-- The rational expression for a third logarithmic derivative. Connecting
`w, w1, w2, w3` to actual derivatives is a separate analytic lemma. -/
def logThirdExpression (w w1 w2 w3 : ℝ) : ℝ :=
  w3 / w - 3 * w1 * w2 / w ^ 2 + 2 * w1 ^ 3 / w ^ 3

/-- The lower-derivative expression isolated in Pang's equation (18). -/
def lowerDerivativeBracket (w w1 w2 : ℝ) : ℝ :=
  -(3 * w2) / w + 2 * w1 ^ 2 / w ^ 2

theorem logThirdExpression_eq (w w1 w2 w3 : ℝ) (hw : w ≠ 0) :
    logThirdExpression w w1 w2 w3 =
      w3 / w + (w1 / w) * lowerDerivativeBracket w w1 w2 := by
  unfold logThirdExpression lowerDerivativeBracket
  field_simp [hw]
  <;> ring

theorem logThirdExpression_neg_of_bounds {w w1 w2 w3 c : ℝ}
    (hw : 0 < w) (hw1 : 0 ≤ w1)
    (hbracket : lowerDerivativeBracket w w1 w2 ≤ c)
    (hsign : w3 + c * w1 < 0) :
    logThirdExpression w w1 w2 w3 < 0 := by
  rw [logThirdExpression_eq w w1 w2 w3 hw.ne']
  have hratio : 0 ≤ w1 / w := div_nonneg hw1 hw.le
  calc
    w3 / w + (w1 / w) * lowerDerivativeBracket w w1 w2
        ≤ w3 / w + (w1 / w) * c := by
          linarith only [mul_le_mul_of_nonneg_left hbracket hratio]
    _ = (w3 + c * w1) / w := by ring
    _ < 0 := div_neg_of_neg_of_pos hsign hw

theorem logThirdExpression_neg_of_pang_bounds {w w1 w2 w3 : ℝ}
    (hw : 0 < w) (hw1 : 0 < w1)
    (hbracket : lowerDerivativeBracket w w1 w2 < 7 / 2)
    (hsign : w3 + (7 / 2) * w1 < 0) :
    logThirdExpression w w1 w2 w3 < 0 :=
  logThirdExpression_neg_of_bounds hw hw1.le hbracket.le hsign

/-- The final rational margin in Pang's Proposition 4.8. -/
theorem signedIntegralMargin_pos {n : ℕ} (hn : 150 ≤ n) :
    0 < (3 / 4 : ℝ) - 1 / 20 - 80 / (n : ℝ) - 1 / 10 := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hdiv : (80 : ℝ) / n ≤ 80 / 150 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  linarith

/-- The final rational margin in Pang's Proposition 4.7. -/
theorem lowerDerivativeMargin_lt {n : ℕ} (hn : 150 ≤ n) :
    (63 / 19 : ℝ) + (8 / (n : ℝ)) * (20 / 19) ^ 2 < 7 / 2 := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hdiv : (8 : ℝ) / n ≤ 8 / 150 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  nlinarith

/-- Separate the numerical use of `n ≥ 150` from the analytic ratio bounds. -/
theorem lowerDerivativeBracket_lt_of_ratios {n : ℕ} {w w1 w2 : ℝ}
    (hn : 150 ≤ n)
    (hsecond : -w2 / w < 21 / 19)
    (hfirst : w1 ^ 2 / w ^ 2 ≤ (4 / (n : ℝ)) * (20 / 19) ^ 2) :
    lowerDerivativeBracket w w1 w2 < 7 / 2 := by
  have hm := lowerDerivativeMargin_lt hn
  unfold lowerDerivativeBracket
  have hsecond' : -(3 * w2) / w < 63 / 19 := by
    calc
      -(3 * w2) / w = 3 * (-w2 / w) := by ring
      _ < 3 * (21 / 19) := mul_lt_mul_of_pos_left hsecond (by norm_num)
      _ = 63 / 19 := by norm_num
  have hfirst' : 2 * w1 ^ 2 / w ^ 2 ≤ (8 / (n : ℝ)) * (20 / 19) ^ 2 := by
    calc
      2 * w1 ^ 2 / w ^ 2 = 2 * (w1 ^ 2 / w ^ 2) := by ring
      _ ≤ 2 * ((4 / (n : ℝ)) * (20 / 19) ^ 2) :=
        mul_le_mul_of_nonneg_left hfirst (by norm_num)
      _ = (8 / (n : ℝ)) * (20 / 19) ^ 2 := by ring
  linarith

end
end ENT.Pang
