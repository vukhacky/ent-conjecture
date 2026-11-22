module

public import ENT.Pang.SineScalar
public import Mathlib.Analysis.Convex.Deriv

/-! The three odd convex test functions used for the signed sine bounds. -/

@[expose] public section

set_option autoImplicit false

open Set

namespace ENT.Pang

noncomputable section

theorem convexOn_Ici_of_hasDerivAt2_nonneg {f g h : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (h x) x)
    (hh : ∀ x, 0 ≤ x → 0 ≤ h x) : ConvexOn ℝ (Ici 0) f := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).hasDerivWithinAt)
    (fun x _ => (hg x).hasDerivWithinAt)
  exact fun x hx => hh x (interior_subset hx)

theorem convexOn_Ici_comp_mul_nonneg {h : ℝ → ℝ} (hc : ConvexOn ℝ (Ici 0) h)
    {u : ℝ} (hu : 0 ≤ u) : ConvexOn ℝ (Ici 0) (fun x => h (u * x)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hc.2 (mul_nonneg hu hx) (mul_nonneg hu hy) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  convert h using 1 <;> congr 1 <;> ring

def cubicSinPlus (x : ℝ) : ℝ := x ^ 3 / 6 + Real.sin x
def cubicSinMinus (x : ℝ) : ℝ := x ^ 3 / 6 - Real.sin x
def fifthSinTest (x : ℝ) : ℝ := x ^ 5 / 120 - x ^ 3 / 6 - Real.sin x

theorem cubicSinPlus_odd (x : ℝ) : cubicSinPlus (-x) = -cubicSinPlus x := by
  unfold cubicSinPlus
  rw [Real.sin_neg]
  ring

theorem cubicSinMinus_odd (x : ℝ) : cubicSinMinus (-x) = -cubicSinMinus x := by
  unfold cubicSinMinus
  rw [Real.sin_neg]
  ring

theorem fifthSinTest_odd (x : ℝ) : fifthSinTest (-x) = -fifthSinTest x := by
  unfold fifthSinTest
  rw [Real.sin_neg]
  ring

theorem hasDerivAt_cubicSinPlus (x : ℝ) :
    HasDerivAt cubicSinPlus (x ^ 2 / 2 + Real.cos x) x := by
  have h := (((hasDerivAt_id x).pow 3).div_const 6).add (Real.hasDerivAt_sin x)
  apply h.congr_deriv
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, id_eq]
  ring

theorem hasDerivAt_cubicSinMinus (x : ℝ) :
    HasDerivAt cubicSinMinus (x ^ 2 / 2 - Real.cos x) x := by
  have h := (((hasDerivAt_id x).pow 3).div_const 6).sub (Real.hasDerivAt_sin x)
  apply h.congr_deriv
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, id_eq]
  ring

theorem hasDerivAt_fifthSinTest (x : ℝ) :
    HasDerivAt fifthSinTest (x ^ 4 / 24 - x ^ 2 / 2 - Real.cos x) x := by
  have h := ((((hasDerivAt_id x).pow 5).div_const 120).sub
    (((hasDerivAt_id x).pow 3).div_const 6)).sub (Real.hasDerivAt_sin x)
  apply h.congr_deriv
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, id_eq]
  ring

theorem convexOn_cubicSinPlus : ConvexOn ℝ (Ici 0) cubicSinPlus := by
  have hg : ∀ x : ℝ, HasDerivAt (fun y => y ^ 2 / 2 + Real.cos y)
      (x - Real.sin x) x := by
    intro x
    have h := (((hasDerivAt_id x).pow 2).div_const 2).add (Real.hasDerivAt_cos x)
    apply h.congr_deriv
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, id_eq]
    ring
  exact convexOn_Ici_of_hasDerivAt2_nonneg hasDerivAt_cubicSinPlus hg
    (fun x hx => sub_nonneg.mpr (Real.sin_le hx))

theorem convexOn_cubicSinMinus : ConvexOn ℝ (Ici 0) cubicSinMinus := by
  have hg : ∀ x : ℝ, HasDerivAt (fun y => y ^ 2 / 2 - Real.cos y)
      (x + Real.sin x) x := by
    intro x
    have h := (((hasDerivAt_id x).pow 2).div_const 2).sub (Real.hasDerivAt_cos x)
    apply h.congr_deriv
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, id_eq]
    ring
  apply convexOn_Ici_of_hasDerivAt2_nonneg hasDerivAt_cubicSinMinus hg
  intro x hx
  have h := Real.abs_sin_le_abs (x := x)
  rw [abs_of_nonneg hx] at h
  linarith [(abs_le.mp h).1]

theorem convexOn_fifthSinTest : ConvexOn ℝ (Ici 0) fifthSinTest := by
  have hg : ∀ x : ℝ, HasDerivAt (fun y => y ^ 4 / 24 - y ^ 2 / 2 - Real.cos y)
      (x ^ 3 / 6 - x + Real.sin x) x := by
    intro x
    have h := ((((hasDerivAt_id x).pow 4).div_const 24).sub
      (((hasDerivAt_id x).pow 2).div_const 2)).sub (Real.hasDerivAt_cos x)
    apply h.congr_deriv
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, id_eq]
    ring
  apply convexOn_Ici_of_hasDerivAt2_nonneg hasDerivAt_fifthSinTest hg
  intro x hx
  linarith [Real.sin_ge_sub_cube hx]

end
end ENT.Pang
