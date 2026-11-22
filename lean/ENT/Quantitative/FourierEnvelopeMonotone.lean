module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! Monotonicity in the dimension of the polynomial Fourier envelope.
All bases and all denominators are strictly positive in the public bounds. -/

@[expose] public section
set_option autoImplicit false
open Set

namespace ENT.Quantitative
noncomputable section

theorem hasDerivAt_dimension_log (v : ℝ) (hv : 0 ≤ v) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y * Real.log (1 + v/y))
      (Real.log (1+v/x) - v/(x+v)) x := by
  have hp : 0 < 1+v/x := by positivity
  have hxp : 0 < x+v := by positivity
  have h := (hasDerivAt_id x).mul
    ((((hasDerivAt_const x v).div (hasDerivAt_id x) hx.ne').const_add 1).log hp.ne')
  convert h using 1
  · rfl
  · simp only [Pi.div_apply, id_eq, one_mul, zero_mul, mul_one, zero_sub]
    generalize Real.log (1+v/x) = L
    field_simp [hx.ne', hxp.ne', hp.ne']
    <;> ring

theorem dimension_log_deriv_nonneg (v : ℝ) (hv : 0 ≤ v) (x : ℝ) (hx : 0 < x) :
    0 ≤ Real.log (1+v/x) - v/(x+v) := by
  have hp : 0 < 1+v/x := by positivity
  have hxp : 0 < x+v := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hp
  have he : 1-(1+v/x)⁻¹ = v/(x+v) := by
    field_simp
    <;> ring
  rw [he] at h
  linarith

theorem dimension_log_monotoneOn (v : ℝ) (hv : 0 ≤ v) :
    MonotoneOn (fun x : ℝ => x * Real.log (1+v/x)) (Ioi 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    (fun x hx => (hasDerivAt_dimension_log v hv x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_dimension_log v hv x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  exact dimension_log_deriv_nonneg v hv x (interior_subset hx)

theorem fourier_envelope_antitone_real {m n : ℝ} (hm : 0 < m) (hmn : m ≤ n)
    (u : ℝ) :
    (1+u^2/n) ^ (-n/2) ≤ (1+u^2/m) ^ (-m/2) := by
  have hn : 0 < n := hm.trans_le hmn
  have h := dimension_log_monotoneOn (u^2) (sq_nonneg u) hm hn hmn
  rw [Real.rpow_def_of_pos (by positivity : 0 < 1+u^2/n),
    Real.rpow_def_of_pos (by positivity : 0 < 1+u^2/m)]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem fourier_envelope_le_fixed {N n : ℕ} (hN : 0 < N) (hNn : N ≤ n)
    (u : ℝ) :
    (1+u^2/(n:ℝ)) ^ (-(n:ℝ)/2) ≤
      (1+u^2/(N:ℝ)) ^ (-(N:ℝ)/2) :=
  fourier_envelope_antitone_real (by exact_mod_cast hN) (by exact_mod_cast hNn) u

end
end ENT.Quantitative
