module

public import ENT.Pang.PositiveODE
public import ENT.Pang.HigherMoments

/-!
# Strict negativity of the fifth centered tilt moment

The certificate consists of twelve exact second-order differential identities.
The first six operators are `D² - 1`; the last six are `D² - 9`. Every value at
zero is zero, every first derivative at zero is nonnegative, and the final
function is a positive multiple of `sinh(5t)`. The table is ordinary input
syntax: its derivative identities and signs are proved by the Lean kernel.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace ENT.Pang

noncomputable section

def fifthSignP5 : ℕ → Polynomial ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | _ => 0

def fifthSignQ5 : ℕ → Polynomial ℝ
  | 0 => 11
  | 1 => 264
  | 2 => 6336
  | 3 => 152064
  | 4 => 3649536
  | 5 => 87588864
  | 6 => 2102132736
  | 7 => 33634123776
  | 8 => 538145980416
  | 9 => 8610335686656
  | 10 => 137765370986496
  | 11 => 2204245935783936
  | _ => 35267934972542976

def fifthSignP3 : ℕ → Polynomial ℝ
  | 0 => -8 * X ^ 5 + -20 * X ^ 3
  | 1 => -64 * X ^ 5 + -320 * X ^ 3 + -360 * X
  | 2 => -512 * X ^ 5 + -9600 * X ^ 3 + -11040 * X
  | 3 => -4096 * X ^ 5 + -179200 * X ^ 3 + -299520 * X
  | 4 => -32768 * X ^ 5 + -2621440 * X ^ 3 + -7326720 * X
  | 5 => -262144 * X ^ 5 + -33423360 * X ^ 3 + -150528000 * X
  | 6 => -2097152 * X ^ 5 + -390594560 * X ^ 3 + -2651258880 * X
  | 7 => -1174405120 * X ^ 3 + -20242759680 * X
  | 8 => -1509949440 * X ^ 3 + -98209628160 * X
  | 9 => -271790899200 * X
  | 10 => -326149079040 * X
  | 11 => 0
  | _ => 0

def fifthSignQ3 : ℕ → Polynomial ℝ
  | 0 => -20 * X ^ 2 + -55
  | 1 => -240 * X ^ 4 + -520 * X ^ 2 + -480
  | 2 => -3840 * X ^ 4 + -12800 * X ^ 2 + -7040
  | 3 => -46080 * X ^ 4 + -321280 * X ^ 2 + -148160
  | 4 => -491520 * X ^ 4 + -6348800 * X ^ 2 + -3624960
  | 5 => -4915200 * X ^ 4 + -103874560 * X ^ 2 + -85657600
  | 6 => -47185920 * X ^ 4 + -1491599360 * X ^ 2 + -1796177920
  | 7 => -62914560 * X ^ 4 + -7596933120 * X ^ 2 + -18890752000
  | 8 => -21894266880 * X ^ 2 + -136650424320
  | 9 => -27179089920 * X ^ 2 + -633046302720
  | 10 => -1685103575040
  | 11 => -1956894474240
  | _ => 0

def fifthSignP1 : ℕ → Polynomial ℝ
  | 0 => -8 * X ^ 5 + 20 * X ^ 3
  | 1 => -160 * X ^ 3 + 360 * X
  | 2 => -640 * X ^ 3 + -480 * X
  | 3 => -11520 * X
  | 4 => -15360 * X
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | _ => 0

def fifthSignQ1 : ℕ → Polynomial ℝ
  | 0 => 60 * X ^ 2 + 110
  | 1 => -80 * X ^ 4 + 120 * X ^ 2 + 120
  | 2 => -1920 * X ^ 2 + 960
  | 3 => -3840 * X ^ 2 + -4800
  | 4 => -30720
  | 5 => -30720
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | _ => 0

def fifthSignOperator (j : ℕ) : ℝ := if j < 6 then 1 else 3

def fifthSignChain (j : ℕ) (t : ℝ) : ℝ :=
  hyperbolicPoly 5 (fifthSignP5 j) (fifthSignQ5 j) t +
    hyperbolicPoly 3 (fifthSignP3 j) (fifthSignQ3 j) t +
    hyperbolicPoly 1 (fifthSignP1 j) (fifthSignQ1 j) t

def fifthSignFirst (j : ℕ) (t : ℝ) : ℝ :=
  hyperbolicPoly 5 ((fifthSignP5 j).derivative + C 5 * fifthSignQ5 j)
      ((fifthSignQ5 j).derivative + C 5 * fifthSignP5 j) t +
    hyperbolicPoly 3 ((fifthSignP3 j).derivative + C 3 * fifthSignQ3 j)
      ((fifthSignQ3 j).derivative + C 3 * fifthSignP3 j) t +
    hyperbolicPoly 1 ((fifthSignP1 j).derivative + C 1 * fifthSignQ1 j)
      ((fifthSignQ1 j).derivative + C 1 * fifthSignP1 j) t

theorem hasDerivAt_fifthSignChain (j : ℕ) (t : ℝ) :
    HasDerivAt (fifthSignChain j) (fifthSignFirst j t) t := by
  exact ((hasDerivAt_hyperbolicPoly 5 (fifthSignP5 j) (fifthSignQ5 j) t).add
    (hasDerivAt_hyperbolicPoly 3 (fifthSignP3 j) (fifthSignQ3 j) t)).add
    (hasDerivAt_hyperbolicPoly 1 (fifthSignP1 j) (fifthSignQ1 j) t)

theorem hasDerivAt_fifthSignFirst (j : Fin 12) (t : ℝ) :
    HasDerivAt (fifthSignFirst j)
      (fifthSignChain (j + 1 : ℕ) t + fifthSignOperator j ^ 2 * fifthSignChain j t) t := by
  have h := ((hasDerivAt_hyperbolicPoly 5
      ((fifthSignP5 j).derivative + C 5 * fifthSignQ5 j)
      ((fifthSignQ5 j).derivative + C 5 * fifthSignP5 j) t).add
    (hasDerivAt_hyperbolicPoly 3
      ((fifthSignP3 j).derivative + C 3 * fifthSignQ3 j)
      ((fifthSignQ3 j).derivative + C 3 * fifthSignP3 j) t)).add
    (hasDerivAt_hyperbolicPoly 1
      ((fifthSignP1 j).derivative + C 1 * fifthSignQ1 j)
      ((fifthSignQ1 j).derivative + C 1 * fifthSignP1 j) t)
  apply h.congr_deriv
  fin_cases j <;>
    norm_num [fifthSignChain, hyperbolicPoly, fifthSignP5, fifthSignQ5, fifthSignP3,
      fifthSignQ3, fifthSignP1, fifthSignQ1, fifthSignOperator,
      derivative_add, derivative_sub, derivative_mul, derivative_pow] <;> ring

theorem fifthSignChain_zero (j : Fin 12) : fifthSignChain j 0 = 0 := by
  fin_cases j <;>
    norm_num [fifthSignChain, hyperbolicPoly, fifthSignP5, fifthSignQ5, fifthSignP3,
      fifthSignQ3, fifthSignP1, fifthSignQ1]

theorem fifthSignFirst_zero_nonneg (j : Fin 12) : 0 ≤ fifthSignFirst j 0 := by
  fin_cases j <;>
    norm_num [fifthSignFirst, hyperbolicPoly, fifthSignP5, fifthSignQ5, fifthSignP3,
      fifthSignQ3, fifthSignP1, fifthSignQ1,
      derivative_add, derivative_sub, derivative_mul, derivative_pow]

theorem fifthSignChain_twelve_pos {t : ℝ} (ht : 0 < t) : 0 < fifthSignChain 12 t := by
  have hs5 : 0 < Real.sinh (5 * t) := Real.sinh_pos_iff.mpr (by linarith)
  norm_num [fifthSignChain, hyperbolicPoly, fifthSignP5, fifthSignQ5, fifthSignP3,
    fifthSignQ3, fifthSignP1, fifthSignQ1]
  positivity

theorem fifthSignChain_pos_of_succ (j : Fin 12)
    (hpos : ∀ t : ℝ, 0 < t → 0 < fifthSignChain (j + 1 : ℕ) t)
    {t : ℝ} (ht : 0 < t) : 0 < fifthSignChain j t := by
  apply positive_of_second_order_operator_of_nonneg_deriv (fifthSignOperator j)
    (hasDerivAt_fifthSignChain j) (hasDerivAt_fifthSignFirst j)
    (fifthSignChain_zero j) (fifthSignFirst_zero_nonneg j) ?_ ht
  intro x hx
  nlinarith [hpos x hx]

theorem fifthSignChain_pos {t : ℝ} (ht : 0 < t) : 0 < fifthSignChain 0 t := by
  have h12 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 12 t :=
    fun _ ht => fifthSignChain_twelve_pos ht
  have h11 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 11 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨11, by decide⟩ h12 ht
  have h10 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 10 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨10, by decide⟩ h11 ht
  have h9 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 9 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨9, by decide⟩ h10 ht
  have h8 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 8 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨8, by decide⟩ h9 ht
  have h7 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 7 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨7, by decide⟩ h8 ht
  have h6 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 6 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨6, by decide⟩ h7 ht
  have h5 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 5 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨5, by decide⟩ h6 ht
  have h4 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 4 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨4, by decide⟩ h5 ht
  have h3 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 3 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨3, by decide⟩ h4 ht
  have h2 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 2 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨2, by decide⟩ h3 ht
  have h1 : ∀ t : ℝ, 0 < t → 0 < fifthSignChain 1 t := fun _ ht =>
    fifthSignChain_pos_of_succ ⟨1, by decide⟩ h2 ht
  exact fifthSignChain_pos_of_succ ⟨0, by decide⟩ h1 ht

theorem fifthSignChain_eq (t : ℝ) :
    fifthSignChain 0 t = 4 * (44 * Real.sinh t ^ 5 -
      8 * t ^ 5 * Real.cosh t * Real.sinh t ^ 2 - 4 * t ^ 5 * Real.cosh t -
      20 * t ^ 3 * Real.cosh t * Real.sinh t ^ 2 - 20 * t ^ 2 * Real.sinh t ^ 3) := by
  have hc3 : Real.cosh t ^ 3 = Real.cosh t * (Real.sinh t ^ 2 + 1) := by
    rw [pow_succ, Real.cosh_sq]
    ring
  have hc4 : Real.cosh t ^ 4 = (Real.sinh t ^ 2 + 1) ^ 2 := by
    calc
      Real.cosh t ^ 4 = (Real.cosh t ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.cosh_sq]
  have hs5 : Real.sinh (5 * t) =
      16 * Real.sinh t ^ 5 + 20 * Real.sinh t ^ 3 + 5 * Real.sinh t := by
    rw [show 5 * t = 2 * t + 3 * t by ring, Real.sinh_add,
      Real.sinh_two_mul, Real.cosh_three_mul, Real.cosh_two_mul, Real.sinh_three_mul]
    ring_nf
    simp only [hc4, Real.cosh_sq]
    ring
  norm_num [fifthSignChain, hyperbolicPoly, fifthSignP5, fifthSignQ5, fifthSignP3,
    fifthSignQ3, fifthSignP1, fifthSignQ1, hs5, Real.cosh_three_mul, Real.sinh_three_mul]
  rw [hc3]
  ring

theorem fifth_moment_sign_identity {t : ℝ} (ht : 0 < t) :
    t ^ 5 * Real.sinh t ^ 5 *
      (tiltFifthCumulant t + 10 * tiltVariance t * tiltThirdCumulant t) =
      -(fifthSignChain 0 t / 4) := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  rw [fifthSignChain_eq]
  unfold tiltVariance tiltThirdCumulant tiltFifthCumulant
  field_simp [ht.ne', hs]
  <;> ring

theorem fifth_central_expression_neg {t : ℝ} (ht : 0 < t) :
    tiltFifthCumulant t + 10 * tiltVariance t * tiltThirdCumulant t < 0 := by
  have hi := fifth_moment_sign_identity ht
  have hp : 0 < fifthSignChain 0 t := fifthSignChain_pos ht
  have hden : 0 < t ^ 5 * Real.sinh t ^ 5 := by
    have hs := Real.sinh_pos_iff.mpr ht
    positivity
  have hm : (t ^ 5 * Real.sinh t ^ 5) *
      (tiltFifthCumulant t + 10 * tiltVariance t * tiltThirdCumulant t) < 0 := by
    rw [hi]
    linarith
  by_contra hn
  have hnonneg := mul_nonneg hden.le (le_of_not_gt hn)
  linarith

theorem tiltCentralMoment_five_neg {t : ℝ} (ht : 0 < t) :
    tiltCentralMoment t 5 < 0 := by
  rw [tiltCentralMoment_five ht]
  exact fifth_central_expression_neg ht

end
end ENT.Pang
