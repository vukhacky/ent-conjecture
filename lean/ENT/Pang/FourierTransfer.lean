module

public import ENT.Pang.FourierAtZero
public import ENT.Pang.TiltLimits
public import ENT.Spline.PositiveInterior
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Transfer of the third logarithmic derivative from the actual standardized
tilted density to the diagonal spline density. -/

@[expose] public section

set_option autoImplicit false

open Set Filter
open scoped Topology

attribute [local instance 1001] NormedField.toNormedSpace

namespace ENT.Pang

noncomputable section

theorem iteratedDeriv_affine_comp (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) :
    iteratedDeriv k (fun x => f (a * x + b)) =
      fun x => a ^ k * iteratedDeriv k f (a * x + b) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [deriv_const_mul_field]
      have h := deriv_comp_mul_left a (fun z => iteratedDeriv k f (z + b)) x
      rw [deriv_comp_add_const] at h
      rw [h]
      simp only [smul_eq_mul, iteratedDeriv_succ, pow_succ]
      ring

theorem tiltCenter_mem_Ioo {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (n : ℝ) * tiltMean t ∈
      Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hm0 := tiltMean_pos ht
  have hm1 := tiltMean_lt_one ht
  constructor
  · exact lt_trans (neg_neg_of_pos hs) (mul_pos hs hm0)
  · simpa only [mul_one] using mul_lt_mul_of_pos_left hm1 hs

theorem standardizedDensity_zero_pos {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    0 < standardizedDensity n t 0 := by
  unfold standardizedDensity tiltedDiagonalDensity
  simp only [mul_zero, zero_add]
  exact mul_pos (Real.sqrt_pos.mpr (tiltVariance_pos ht))
    (mul_pos (Spline.diagonalSplineDensity_pos n hn _ (tiltCenter_mem_Ioo (by omega) ht))
      (mul_pos (pow_pos (tiltNormalizer_pos ht) _) (Real.exp_pos _)))

def standardizedPotential (n : ℕ) (t x : ℝ) : ℝ :=
  -Real.log (standardizedDensity n t x)

theorem standardizedPotential_eventuallyEq {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : 0 < t) :
    standardizedPotential n t =ᶠ[𝓝 (0 : ℝ)]
      (fun x =>
        (-Real.log (Real.sqrt (tiltVariance t)) - Real.log (tiltNormalizer t ^ n) -
          t * Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) * tiltMean t)) +
        (-(t * Real.sqrt (n : ℝ) * Real.sqrt (tiltVariance t)) * x +
          Spline.diagonalSplinePotential n
            (Real.sqrt (tiltVariance t) * x + Real.sqrt (n : ℝ) * tiltMean t))) := by
  have hs : Real.sqrt (tiltVariance t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (tiltVariance_pos ht))
  have hc : tiltNormalizer t ^ n ≠ 0 := ne_of_gt (pow_pos (tiltNormalizer_pos ht) _)
  have hcont : Continuous (fun x : ℝ => Spline.diagonalSplineDensity n
      (Real.sqrt (tiltVariance t) * x + Real.sqrt (n : ℝ) * tiltMean t)) :=
    (Spline.continuous_diagonalSplineDensity n).comp (by fun_prop)
  have hq : Spline.diagonalSplineDensity n
      (Real.sqrt (tiltVariance t) * 0 + Real.sqrt (n : ℝ) * tiltMean t) ≠ 0 := by
    simpa only [mul_zero, zero_add] using
      ne_of_gt (Spline.diagonalSplineDensity_pos n hn _ (tiltCenter_mem_Ioo (by omega) ht))
  filter_upwards [hcont.continuousAt.eventually_ne hq] with x hx
  unfold standardizedPotential standardizedDensity tiltedDiagonalDensity
  rw [Real.log_mul hs (mul_ne_zero hx (mul_ne_zero hc (Real.exp_ne_zero _))),
    Real.log_mul hx (mul_ne_zero hc (Real.exp_ne_zero _)),
    Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
  unfold Spline.diagonalSplinePotential
  ring

theorem standardizedPotential_third_deriv {n : ℕ} (hn : 5 ≤ n)
    {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 3 (standardizedPotential n t) 0 =
      Real.sqrt (tiltVariance t) ^ 3 *
        iteratedDeriv 3 (Spline.diagonalSplinePotential n)
          (Real.sqrt (n : ℝ) * tiltMean t) := by
  have hq := Spline.diagonalSplineDensity_pos n (by omega) _
    (tiltCenter_mem_Ioo (by omega) ht)
  have hV : ContDiffAt ℝ 3 (fun x : ℝ => Spline.diagonalSplinePotential n
      (Real.sqrt (tiltVariance t) * x + Real.sqrt (n : ℝ) * tiltMean t)) 0 := by
    have hbase : ContDiffAt ℝ 3 (Spline.diagonalSplinePotential n)
        (Real.sqrt (tiltVariance t) * 0 + Real.sqrt (n : ℝ) * tiltMean t) := by
      simpa using
        Spline.contDiffAt_diagonalSplinePotential 3 n (by omega) _ (ne_of_gt hq)
    exact ContDiffAt.comp 0 (g := Spline.diagonalSplinePotential n)
      (f := fun x : ℝ => Real.sqrt (tiltVariance t) * x + Real.sqrt (n : ℝ) * tiltMean t)
      hbase (by fun_prop)
  have h := (standardizedPotential_eventuallyEq (by omega : 2 ≤ n) ht).iteratedDeriv_eq 3
  rw [iteratedDeriv_const_add (by norm_num : 0 < (3 : ℕ)),
    iteratedDeriv_fun_add (by fun_prop) hV, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_id] at h
  norm_num only [OfNat.ofNat_ne_zero, Nat.reduceEqDiff, ite_false, mul_zero, zero_add] at h
  rw [iteratedDeriv_affine_comp] at h
  simpa only [mul_zero, zero_add] using h

theorem diagonalPotential_third_deriv_tilt {n : ℕ} (hn : 5 ≤ n)
    {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 3 (Spline.diagonalSplinePotential n)
        (Real.sqrt (n : ℝ) * tiltMean t) =
      (Real.sqrt (tiltVariance t) ^ 3)⁻¹ *
        iteratedDeriv 3 (standardizedPotential n t) 0 := by
  rw [standardizedPotential_third_deriv hn ht]
  have hs : Real.sqrt (tiltVariance t) ^ 3 ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.mpr (tiltVariance_pos ht)))
  rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

theorem existsUnique_tiltCenter {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (Real.sqrt (n : ℝ))) :
    ∃! t : ℝ, 0 < t ∧ Real.sqrt (n : ℝ) * tiltMean t = x := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hm : x / Real.sqrt (n : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hx.1 hs, (div_lt_one hs).mpr hx.2⟩
  obtain ⟨t, ht, huniq⟩ := existsUnique_positive_tilt hm
  refine ⟨t, ⟨ht.1, ?_⟩, ?_⟩
  · rw [ht.2]
    field_simp
  · intro u hu
    apply huniq u
    refine ⟨hu.1, ?_⟩
    apply (eq_div_iff hs.ne').mpr
    simpa only [mul_comm] using hu.2

theorem diagonalPotential_third_deriv_pos_of_tilt {n : ℕ} (hn : 5 ≤ n)
    (h : ∀ t : ℝ, 0 < t → 0 < iteratedDeriv 3 (standardizedPotential n t) 0) :
    ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt (n : ℝ)),
      0 < iteratedDeriv 3 (Spline.diagonalSplinePotential n) x := by
  intro x hx
  obtain ⟨t, ht, _⟩ := existsUnique_tiltCenter (by omega) hx
  rw [← ht.2, diagonalPotential_third_deriv_tilt hn ht.1]
  exact mul_pos (inv_pos.mpr (pow_pos (Real.sqrt_pos.mpr (tiltVariance_pos ht.1)) _))
    (h t ht.1)

end
end ENT.Pang
