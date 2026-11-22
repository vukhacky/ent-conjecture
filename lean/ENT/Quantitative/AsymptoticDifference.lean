module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! A third-order entropy expansion controls the difference between consecutive dimensions. -/

@[expose] public section
set_option autoImplicit false
open Filter
open scoped Topology

namespace ENT.Quantitative

private theorem tendsto_nat_inv :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private theorem tendsto_nat_add_one_inv :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    tendsto_nat_inv.comp (tendsto_add_atTop_nat 1)

/-- The remainder hypothesis is precisely `r_n = o(n⁻³)` in scaled form. It
controls the adjacent difference without any monotonicity assumption on `r`. -/
theorem scaled_remainder_forward_difference {r : ℕ → ℝ}
    (hr : Tendsto (fun n : ℕ => (n : ℝ)^3 * r n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)^2 * (n : ℝ) * (r n - r (n + 1)))
      atTop (𝓝 0) := by
  have hleft : Tendsto
      (fun n : ℕ => (1 + (n : ℝ)⁻¹)^2 * ((n : ℝ)^3 * r n)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds.add tendsto_nat_inv).pow 2).mul hr
  have hrnext : Tendsto (fun n : ℕ => (n + 1 : ℝ)^3 * r (n + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hr.comp (tendsto_add_atTop_nat 1)
  have hright : Tendsto
      (fun n : ℕ => (1 - (n + 1 : ℝ)⁻¹) * ((n + 1 : ℝ)^3 * r (n + 1)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.sub tendsto_nat_add_one_inv).mul hrnext
  have hdiff := hleft.sub hright
  simp only [sub_self] at hdiff
  apply hdiff.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- An `n⁻² + n⁻³ + o(n⁻³)` expansion has the exact scaled adjacent-difference
limit `2*c₂`. In particular, the unspecified cubic coefficient cancels. -/
theorem scaled_forward_difference_of_order_three
    (D : ℕ → ℝ) (c₂ c₃ : ℝ)
    (h : Tendsto (fun n : ℕ => (n : ℝ)^3 *
      (D n - c₂ / (n : ℝ)^2 - c₃ / (n : ℝ)^3)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)^2 * (n : ℝ) * (D n - D (n + 1)))
      atTop (𝓝 (2 * c₂)) := by
  let r : ℕ → ℝ := fun n => D n - c₂ / (n : ℝ)^2 - c₃ / (n : ℝ)^3
  have hr : Tendsto (fun n : ℕ => (n : ℝ)^3 * r n) atTop (𝓝 0) := h
  have hrem := scaled_remainder_forward_difference hr
  have hquad : Tendsto (fun n : ℕ => c₂ * (2 + (n : ℝ)⁻¹)) atTop (𝓝 (2 * c₂)) := by
    simpa [mul_comm] using tendsto_const_nhds.mul (tendsto_const_nhds.add tendsto_nat_inv)
  have hcubic : Tendsto (fun n : ℕ =>
      c₃ * (3 + 3 * (n : ℝ)⁻¹ + ((n : ℝ)⁻¹)^2) * (n + 1 : ℝ)⁻¹)
      atTop (𝓝 0) := by
    have hpoly : Tendsto (fun n : ℕ =>
        3 + 3 * (n : ℝ)⁻¹ + ((n : ℝ)⁻¹)^2) atTop (𝓝 3) := by
      simpa using ((tendsto_nat_inv.const_mul (3 : ℝ)).const_add 3).add
        (tendsto_nat_inv.pow 2)
    simpa using (tendsto_const_nhds.mul hpoly).mul tendsto_nat_add_one_inv
  have hall := (hquad.add hcubic).add hrem
  simp only [add_zero] at hall
  apply hall.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  dsimp [r]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

/-- A conventional little-o hypothesis implies the scaled remainder condition.
The exceptional value at `n = 0` is immaterial to the limit. -/
theorem scaled_remainder_tendsto_of_isLittleO {r : ℕ → ℝ}
    (hr : r =o[atTop] (fun n : ℕ => ((n : ℝ)^3)⁻¹)) :
    Tendsto (fun n : ℕ => (n : ℝ)^3 * r n) atTop (𝓝 0) := by
  convert hr.tendsto_div_nhds_zero using 1
  funext n
  simp [div_eq_mul_inv, mul_comm]

theorem scaled_forward_difference_of_littleO
    (D : ℕ → ℝ) (c₂ c₃ : ℝ)
    (h : (fun n : ℕ => D n - c₂ / (n : ℝ)^2 - c₃ / (n : ℝ)^3)
      =o[atTop] (fun n : ℕ => ((n : ℝ)^3)⁻¹)) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)^2 * (n : ℝ) * (D n - D (n + 1)))
      atTop (𝓝 (2 * c₂)) :=
  scaled_forward_difference_of_order_three D c₂ c₃
    (scaled_remainder_tendsto_of_isLittleO h)

end ENT.Quantitative
