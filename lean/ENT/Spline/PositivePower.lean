module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-! Truncated positive powers, including differentiability at the knot zero.
One-sided derivatives are glued before asserting a global derivative. -/

@[expose] public section

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace ENT.Spline

noncomputable section

def positivePower (m : ℕ) (x : ℝ) : ℝ := (max 0 x) ^ m

theorem continuous_positivePower (m : ℕ) : Continuous (positivePower m) :=
  (continuous_const.max continuous_id).pow m

theorem positivePower_add_two_hasDerivAt_zero (m : ℕ) :
    HasDerivAt (positivePower (m + 2)) 0 0 := by
  have hl : HasDerivWithinAt (positivePower (m + 2)) 0 (Iic 0) 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
    · intro y hy
      simp [positivePower, max_eq_left (show y ≤ 0 from hy)]
    · simp [positivePower]
  have hpow : HasDerivAt (fun y : ℝ => y ^ (m + 2)) 0 0 := by
    convert hasDerivAt_pow (m + 2) (0 : ℝ) using 1 <;> simp
  have hr : HasDerivWithinAt (positivePower (m + 2)) 0 (Ici 0) 0 := by
    apply hpow.hasDerivWithinAt.congr
    · intro y hy
      simp [positivePower, max_eq_right (show 0 ≤ y from hy)]
    · simp [positivePower]
  have h := hl.union hr
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using h

theorem positivePower_add_two_hasDerivAt (m : ℕ) (x : ℝ) :
    HasDerivAt (positivePower (m + 2))
      ((m + 2 : ℕ) * positivePower (m + 1) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hne : ∀ᶠ y in 𝓝 x, y < 0 := Iio_mem_nhds hx
    have heq : positivePower (m + 2) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
      hne.mono (fun y hy => by
        simp [positivePower, max_eq_left (show y ≤ 0 from le_of_lt hy)])
    have h := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
    simpa [positivePower, max_eq_left hx.le] using h
  · simpa [positivePower] using positivePower_add_two_hasDerivAt_zero m
  · have hne : ∀ᶠ y in 𝓝 x, 0 < y := Ioi_mem_nhds hx
    have heq : positivePower (m + 2) =ᶠ[𝓝 x] (fun y => y ^ (m + 2)) :=
      hne.mono (fun y hy => by
        simp [positivePower, max_eq_right (show 0 ≤ y from le_of_lt hy)])
    have h := (hasDerivAt_pow (m + 2) x).congr_of_eventuallyEq heq
    simpa [positivePower, max_eq_right hx.le] using h

theorem positivePower_hasDerivAt (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    HasDerivAt (positivePower m) ((m : ℝ) * positivePower (m - 1) x) x := by
  have hm' : m - 2 + 2 = m := by omega
  have hm'' : m - 2 + 1 = m - 1 := by omega
  simpa only [hm', hm''] using positivePower_add_two_hasDerivAt (m - 2) x

theorem deriv_positivePower (m : ℕ) (hm : 2 ≤ m) :
    deriv (positivePower m) = fun x => (m : ℝ) * positivePower (m - 1) x := by
  funext x
  exact (positivePower_hasDerivAt m hm x).deriv

theorem contDiff_positivePower (r m : ℕ) (hrm : r < m) :
    ContDiff ℝ r (positivePower m) := by
  induction r generalizing m with
  | zero => exact contDiff_zero.mpr (continuous_positivePower m)
  | succ r ih =>
      have hm : 2 ≤ m := by omega
      have hord : ((r + 1 : ℕ) : ℕ∞ω) = (r : ℕ∞ω) + 1 := by simp
      rw [hord, contDiff_succ_iff_deriv]
      refine ⟨fun x => (positivePower_hasDerivAt m hm x).differentiableAt, ?_, ?_⟩
      · simp
      · rw [deriv_positivePower m hm]
        exact contDiff_const.mul (ih (m - 1) (by omega))

end
end ENT.Spline
