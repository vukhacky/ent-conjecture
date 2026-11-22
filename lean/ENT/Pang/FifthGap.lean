module

public import ENT.Pang.HyperbolicPolynomial
public import ENT.Pang.MomentAlgebra
public import ENT.Pang.SkewSign

/-!
# A finite analytic certificate for Pang's fifth-cumulant gap

Eight differentiations reduce the cleared hyperbolic expression to an
expression with positive coefficients. All lower initial values vanish.
This replaces an infinite-series positivity argument by a finite chain of
ordinary derivative identities, proved inside Lean.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace ENT.Pang

noncomputable section

def fifthGapP : ℕ → Polynomial ℝ
  | 0 => X ^ 3 - 3 * X
  | 1 => 3 * X ^ 2 - 12
  | 2 => 9 * X ^ 3 - 21 * X
  | 3 => 81 * X ^ 2 - 156
  | 4 => 81 * X ^ 3 + 81 * X
  | 5 => 1215 * X ^ 2 - 1404
  | 6 => 729 * X ^ 3 + 5103 * X
  | 7 => 15309 * X ^ 2 - 4860
  | _ => 6561 * X ^ 3 + 102789 * X

def fifthGapQ : ℕ → Polynomial ℝ
  | 0 => -3
  | 1 => 3 * X ^ 3 - 9 * X
  | 2 => 18 * X ^ 2 - 45
  | 3 => 27 * X ^ 3 - 27 * X
  | 4 => 324 * X ^ 2 - 495
  | 5 => 243 * X ^ 3 + 891 * X
  | 6 => 4374 * X ^ 2 - 3321
  | 7 => 2187 * X ^ 3 + 24057 * X
  | _ => 52488 * X ^ 2 + 9477

def fifthGapR : ℕ → Polynomial ℝ
  | 0 => 23 * X ^ 3 + 3 * X
  | 1 => 69 * X ^ 2 + 12
  | 2 => 23 * X ^ 3 + 141 * X
  | 3 => 207 * X ^ 2 + 156
  | 4 => 23 * X ^ 3 + 831 * X
  | 5 => 345 * X ^ 2 + 1404
  | 6 => 23 * X ^ 3 + 2073 * X
  | 7 => 483 * X ^ 2 + 4860
  | _ => 23 * X ^ 3 + 3867 * X

def fifthGapS : ℕ → Polynomial ℝ
  | 0 => 9
  | 1 => 23 * X ^ 3 + 3 * X
  | 2 => 138 * X ^ 2 + 15
  | 3 => 23 * X ^ 3 + 417 * X
  | 4 => 276 * X ^ 2 + 573
  | 5 => 23 * X ^ 3 + 1383 * X
  | 6 => 414 * X ^ 2 + 2787
  | 7 => 23 * X ^ 3 + 2901 * X
  | _ => 552 * X ^ 2 + 7761

def fifthGapChain (j : ℕ) (t : ℝ) : ℝ :=
  hyperbolicPoly 3 (fifthGapP j) (fifthGapQ j) t +
    hyperbolicPoly 1 (fifthGapR j) (fifthGapS j) t

theorem hasDerivAt_fifthGapChain (j : Fin 8) (t : ℝ) :
    HasDerivAt (fifthGapChain j) (fifthGapChain (j + 1 : ℕ) t) t := by
  have h := (hasDerivAt_hyperbolicPoly 3 (fifthGapP j) (fifthGapQ j) t).add
    (hasDerivAt_hyperbolicPoly 1 (fifthGapR j) (fifthGapS j) t)
  apply h.congr_deriv
  fin_cases j <;>
    norm_num [fifthGapChain, hyperbolicPoly, fifthGapP, fifthGapQ, fifthGapR, fifthGapS,
      derivative_add, derivative_sub, derivative_mul, derivative_pow] <;> ring

theorem fifthGapChain_zero (j : Fin 8) : fifthGapChain j 0 = 0 := by
  fin_cases j <;>
    norm_num [fifthGapChain, hyperbolicPoly, fifthGapP, fifthGapQ, fifthGapR, fifthGapS]

theorem fifthGapChain_eight_pos {t : ℝ} (ht : 0 < t) : 0 < fifthGapChain 8 t := by
  have hs3 : 0 < Real.sinh (3 * t) := Real.sinh_pos_iff.mpr (by linarith)
  have hs1 : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hc3 : 0 < Real.cosh (3 * t) := Real.cosh_pos _
  have hc1 : 0 < Real.cosh t := Real.cosh_pos _
  norm_num [fifthGapChain, hyperbolicPoly, fifthGapP, fifthGapQ, fifthGapR, fifthGapS]
  positivity

theorem fifthGapChain_pos_of_succ (j : Fin 8)
    (hpos : ∀ t : ℝ, 0 < t → 0 < fifthGapChain (j + 1 : ℕ) t)
    {t : ℝ} (ht : 0 < t) : 0 < fifthGapChain j t :=
  positive_of_positive_derivative (hasDerivAt_fifthGapChain j) (fifthGapChain_zero j)
    hpos ht

theorem fifthGapChain_pos {t : ℝ} (ht : 0 < t) : 0 < fifthGapChain 0 t := by
  have h8 : ∀ t : ℝ, 0 < t → 0 < fifthGapChain 8 t := fun _ ht => fifthGapChain_eight_pos ht
  have h7 : ∀ t : ℝ, 0 < t → 0 < fifthGapChain 7 t := fun _ ht =>
    fifthGapChain_pos_of_succ ⟨7, by decide⟩ h8 ht
  have h6 : ∀ t : ℝ, 0 < t → 0 < fifthGapChain 6 t := fun _ ht =>
    fifthGapChain_pos_of_succ ⟨6, by decide⟩ h7 ht
  have h5 : ∀ t : ℝ, 0 < t → 0 < fifthGapChain 5 t := fun _ ht =>
    fifthGapChain_pos_of_succ ⟨5, by decide⟩ h6 ht
  have h4 : ∀ t : ℝ, 0 < t → 0 < fifthGapChain 4 t := fun _ ht =>
    fifthGapChain_pos_of_succ ⟨4, by decide⟩ h5 ht
  have h3 : ∀ t : ℝ, 0 < t → 0 < fifthGapChain 3 t := fun _ ht =>
    fifthGapChain_pos_of_succ ⟨3, by decide⟩ h4 ht
  have h2 : ∀ t : ℝ, 0 < t → 0 < fifthGapChain 2 t := fun _ ht =>
    fifthGapChain_pos_of_succ ⟨2, by decide⟩ h3 ht
  have h1 : ∀ t : ℝ, 0 < t → 0 < fifthGapChain 1 t := fun _ ht =>
    fifthGapChain_pos_of_succ ⟨1, by decide⟩ h2 ht
  exact fifthGapChain_pos_of_succ ⟨0, by decide⟩ h1 ht

theorem fifthGapChain_eq (t : ℝ) :
    2 * fifthGapChain 0 t =
      8 * t * (t ^ 2 - 3) * Real.cosh t * Real.sinh t ^ 2 +
        48 * t ^ 3 * Real.cosh t - 24 * Real.sinh t ^ 3 := by
  norm_num [fifthGapChain, hyperbolicPoly, fifthGapP, fifthGapQ, fifthGapR, fifthGapS,
    Real.cosh_three_mul, Real.sinh_three_mul]
  have hc3 : Real.cosh t ^ 3 = Real.cosh t * (Real.sinh t ^ 2 + 1) := by
    rw [pow_succ, Real.cosh_sq]
    ring
  rw [hc3]
  ring

theorem fifth_cumulant_gap_pos {t : ℝ} (ht : 0 < t) :
    0 < tiltFifthCumulant t - 12 * tiltVariance t * tiltThirdCumulant t := by
  have h := fifth_cumulant_gap_identity ht
  rw [← fifthGapChain_eq] at h
  have hp : 0 < 2 * fifthGapChain 0 t := mul_pos (by norm_num) (fifthGapChain_pos ht)
  have hden : 0 < t ^ 3 * Real.sinh t ^ 5 := by
    have hs := Real.sinh_pos_iff.mpr ht
    positivity
  have hm : 0 < (t ^ 3 * Real.sinh t ^ 5) *
      (tiltFifthCumulant t - 12 * tiltVariance t * tiltThirdCumulant t) := by
    rwa [h]
  exact (mul_pos_iff_of_pos_left hden).mp hm

theorem explicit_fifth_ratio_lt_twentyTwo {t : ℝ} (ht : 0 < t) :
    10 + tiltFifthCumulant t / (tiltVariance t * tiltThirdCumulant t) < 22 :=
  fifth_ratio_lt_twentyTwo (tiltVariance_pos ht) (tiltThirdCumulant_neg ht)
    (fifth_cumulant_gap_pos ht)

end
end ENT.Pang
