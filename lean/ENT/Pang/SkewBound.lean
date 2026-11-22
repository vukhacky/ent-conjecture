module

public import ENT.Pang.PositiveODE
public import ENT.Pang.SkewSign

/-!
# A self-contained skewness bound for the tilted uniform law

Five applications of `D² - 4` reduce the denominator-cleared inequality to
a positive expression. The inverse implication is proved using integrating
factors in `PositiveODE`. No general log-concave skewness theorem is assumed.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace ENT.Pang

noncomputable section

def skewBoundP : ℕ → Polynomial ℝ
  | 0 => -3
  | 1 => -20
  | 2 => -48
  | 3 => 1728
  | 4 => 48384
  | _ => 912384

def skewBoundQ : ℕ → Polynomial ℝ
  | 0 => 2 * X
  | 1 => 24 * X
  | 2 => 288 * X
  | 3 => 3456 * X
  | 4 => 41472 * X
  | _ => 497664 * X

def skewBoundR : ℕ → Polynomial ℝ
  | 0 => -4 * X ^ 4 + 12 * X ^ 2 + 12
  | 1 => 8 - 48 * X ^ 2
  | 2 => 288 - 768 * X ^ 2
  | 3 => -4608
  | 4 => -24576
  | _ => 0

def skewBoundS : ℕ → Polynomial ℝ
  | 0 => -4 * X
  | 1 => -64 * X ^ 3 + 96 * X
  | 2 => -768 * X
  | 3 => -6144 * X
  | _ => 0

def skewBoundA : ℕ → Polynomial ℝ
  | 0 => -12 * X ^ 4 - 12 * X ^ 2 - 9
  | 1 => 48 * X ^ 4 - 96 * X ^ 2 + 12
  | 2 => -192 * X ^ 4 + 960 * X ^ 2 - 240
  | 3 => 768 * X ^ 4 - 6144 * X ^ 2 + 2880
  | 4 => -3072 * X ^ 4 + 33792 * X ^ 2 - 23808
  | _ => 12288 * X ^ 4 - 172032 * X ^ 2 + 162816

def skewBoundChain (j : ℕ) (t : ℝ) : ℝ :=
  hyperbolicPoly 4 (skewBoundP j) (skewBoundQ j) t +
    hyperbolicPoly 2 (skewBoundR j) (skewBoundS j) t + (skewBoundA j).eval t

def skewBoundFirst (j : ℕ) (t : ℝ) : ℝ :=
  hyperbolicPoly 4 ((skewBoundP j).derivative + C 4 * skewBoundQ j)
      ((skewBoundQ j).derivative + C 4 * skewBoundP j) t +
    hyperbolicPoly 2 ((skewBoundR j).derivative + C 2 * skewBoundS j)
      ((skewBoundS j).derivative + C 2 * skewBoundR j) t +
    (skewBoundA j).derivative.eval t

theorem hasDerivAt_skewBoundChain (j : ℕ) (t : ℝ) :
    HasDerivAt (skewBoundChain j) (skewBoundFirst j t) t := by
  exact ((hasDerivAt_hyperbolicPoly 4 (skewBoundP j) (skewBoundQ j) t).add
    (hasDerivAt_hyperbolicPoly 2 (skewBoundR j) (skewBoundS j) t)).add
    ((skewBoundA j).hasDerivAt t)

theorem hasDerivAt_skewBoundFirst (j : Fin 5) (t : ℝ) :
    HasDerivAt (skewBoundFirst j)
      (skewBoundChain (j + 1 : ℕ) t + 4 * skewBoundChain j t) t := by
  have h := ((hasDerivAt_hyperbolicPoly 4
      ((skewBoundP j).derivative + C 4 * skewBoundQ j)
      ((skewBoundQ j).derivative + C 4 * skewBoundP j) t).add
    (hasDerivAt_hyperbolicPoly 2
      ((skewBoundR j).derivative + C 2 * skewBoundS j)
      ((skewBoundS j).derivative + C 2 * skewBoundR j) t)).add
    ((skewBoundA j).derivative.hasDerivAt t)
  apply h.congr_deriv
  fin_cases j <;>
    norm_num [skewBoundChain, hyperbolicPoly, skewBoundP, skewBoundQ, skewBoundR,
      skewBoundS, skewBoundA, derivative_add, derivative_sub, derivative_mul,
      derivative_pow] <;> ring

theorem skewBoundChain_zero (j : Fin 5) : skewBoundChain j 0 = 0 := by
  fin_cases j <;>
    norm_num [skewBoundChain, hyperbolicPoly, skewBoundP, skewBoundQ, skewBoundR,
      skewBoundS, skewBoundA]

theorem skewBoundFirst_zero (j : Fin 5) : skewBoundFirst j 0 = 0 := by
  fin_cases j <;>
    norm_num [skewBoundFirst, hyperbolicPoly, skewBoundP, skewBoundQ, skewBoundR,
      skewBoundS, skewBoundA, derivative_add, derivative_sub, derivative_mul,
      derivative_pow]

theorem skewBoundChain_five_pos {t : ℝ} (ht : 0 < t) : 0 < skewBoundChain 5 t := by
  have hc : 1 ≤ Real.cosh (4 * t) := Real.one_le_cosh _
  have hs : 0 ≤ t * Real.sinh (4 * t) :=
    mul_nonneg ht.le (Real.sinh_pos_iff.mpr (by linarith)).le
  norm_num [skewBoundChain, hyperbolicPoly, skewBoundP, skewBoundQ, skewBoundR,
    skewBoundS, skewBoundA]
  nlinarith [sq_nonneg (t ^ 2 - 7)]

theorem skewBoundChain_pos_of_succ (j : Fin 5)
    (hpos : ∀ t : ℝ, 0 < t → 0 < skewBoundChain (j + 1 : ℕ) t)
    {t : ℝ} (ht : 0 < t) : 0 < skewBoundChain j t := by
  apply positive_of_second_order_operator 2 (hasDerivAt_skewBoundChain j)
    (hasDerivAt_skewBoundFirst j) (skewBoundChain_zero j) (skewBoundFirst_zero j) ?_ ht
  intro x hx
  nlinarith [hpos x hx]

theorem skewBoundChain_pos {t : ℝ} (ht : 0 < t) : 0 < skewBoundChain 0 t := by
  have h5 : ∀ t : ℝ, 0 < t → 0 < skewBoundChain 5 t :=
    fun _ ht => skewBoundChain_five_pos ht
  have h4 : ∀ t : ℝ, 0 < t → 0 < skewBoundChain 4 t := fun _ ht =>
    skewBoundChain_pos_of_succ ⟨4, by decide⟩ h5 ht
  have h3 : ∀ t : ℝ, 0 < t → 0 < skewBoundChain 3 t := fun _ ht =>
    skewBoundChain_pos_of_succ ⟨3, by decide⟩ h4 ht
  have h2 : ∀ t : ℝ, 0 < t → 0 < skewBoundChain 2 t := fun _ ht =>
    skewBoundChain_pos_of_succ ⟨2, by decide⟩ h3 ht
  have h1 : ∀ t : ℝ, 0 < t → 0 < skewBoundChain 1 t := fun _ ht =>
    skewBoundChain_pos_of_succ ⟨1, by decide⟩ h2 ht
  exact skewBoundChain_pos_of_succ ⟨0, by decide⟩ h1 ht

def skewSquareGap (t : ℝ) : ℝ :=
  -3 * Real.sinh t ^ 4 + 2 * t * Real.cosh t * Real.sinh t ^ 3 +
    3 * t ^ 2 * Real.sinh t ^ 2 - (Real.cosh t ^ 2 + 1) * t ^ 4

theorem skewBoundChain_eq (t : ℝ) : skewBoundChain 0 t = 8 * skewSquareGap t := by
  have hc4 : Real.cosh (4 * t) =
      (Real.cosh t ^ 2 + Real.sinh t ^ 2) ^ 2 + (2 * Real.sinh t * Real.cosh t) ^ 2 := by
    rw [show 4 * t = 2 * (2 * t) by ring, Real.cosh_two_mul,
      Real.cosh_two_mul, Real.sinh_two_mul]
  have hs4 : Real.sinh (4 * t) =
      2 * (2 * Real.sinh t * Real.cosh t) * (Real.cosh t ^ 2 + Real.sinh t ^ 2) := by
    rw [show 4 * t = 2 * (2 * t) by ring, Real.sinh_two_mul,
      Real.sinh_two_mul, Real.cosh_two_mul]
  norm_num [skewBoundChain, hyperbolicPoly, skewBoundP, skewBoundQ, skewBoundR,
    skewBoundS, skewBoundA, skewSquareGap, hc4, hs4, Real.cosh_two_mul,
    Real.sinh_two_mul, Real.cosh_sq]
  ring_nf
  rw [Real.cosh_sq]
  ring

theorem skewSquareGap_pos {t : ℝ} (ht : 0 < t) : 0 < skewSquareGap t := by
  have h := skewBoundChain_pos ht
  rw [skewBoundChain_eq] at h
  linarith

theorem skew_square_gap_identity {t : ℝ} (ht : 0 < t) :
    t ^ 4 * Real.sinh t ^ 6 *
      (4 * tiltVariance t ^ 3 - tiltThirdCumulant t ^ 2) = 4 * skewSquareGap t := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  unfold tiltVariance tiltThirdCumulant skewSquareGap
  field_simp [ht.ne', hs]
  <;> ring

theorem tiltThirdCumulant_sq_lt {t : ℝ} (ht : 0 < t) :
    tiltThirdCumulant t ^ 2 < 4 * tiltVariance t ^ 3 := by
  have h := skew_square_gap_identity ht
  have hp : 0 < 4 * skewSquareGap t := mul_pos (by norm_num) (skewSquareGap_pos ht)
  have hden : 0 < t ^ 4 * Real.sinh t ^ 6 := by
    have hs := Real.sinh_pos_iff.mpr ht
    positivity
  have hm : 0 < (t ^ 4 * Real.sinh t ^ 6) *
      (4 * tiltVariance t ^ 3 - tiltThirdCumulant t ^ 2) := by
    rwa [h]
  have hg := (mul_pos_iff_of_pos_left hden).mp hm
  linarith

/-- The standardized third centered moment in terms of the variance. -/
def tiltSkewness (t : ℝ) : ℝ :=
  tiltThirdCumulant t / (Real.sqrt (tiltVariance t)) ^ 3

theorem tiltSkewness_neg {t : ℝ} (ht : 0 < t) : tiltSkewness t < 0 := by
  unfold tiltSkewness
  exact div_neg_of_neg_of_pos (tiltThirdCumulant_neg ht)
    (pow_pos (Real.sqrt_pos.2 (tiltVariance_pos ht)) 3)

theorem neg_two_lt_tiltSkewness {t : ℝ} (ht : 0 < t) : -2 < tiltSkewness t := by
  have hv : 0 < tiltVariance t := tiltVariance_pos ht
  have hd : 0 < Real.sqrt (tiltVariance t) ^ 3 := pow_pos (Real.sqrt_pos.2 hv) 3
  have hs : (Real.sqrt (tiltVariance t) ^ 3) ^ 2 = tiltVariance t ^ 3 := by
    calc
      (Real.sqrt (tiltVariance t) ^ 3) ^ 2 =
          (Real.sqrt (tiltVariance t) ^ 2) ^ 3 := by ring
      _ = _ := by rw [Real.sq_sqrt hv.le]
  have hk := tiltThirdCumulant_sq_lt ht
  have hb : -2 * (Real.sqrt (tiltVariance t) ^ 3) < tiltThirdCumulant t := by
    nlinarith [sq_nonneg (tiltThirdCumulant t + 2 * Real.sqrt (tiltVariance t) ^ 3)]
  unfold tiltSkewness
  exact (lt_div_iff₀ hd).mpr hb

theorem tiltSkewness_mem_Ioo {t : ℝ} (ht : 0 < t) :
    tiltSkewness t ∈ Set.Ioo (-2 : ℝ) 0 :=
  ⟨neg_two_lt_tiltSkewness ht, tiltSkewness_neg ht⟩

end
end ENT.Pang
