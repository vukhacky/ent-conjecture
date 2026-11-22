module

public import ENT.Pang.HyperbolicPolynomial

/-! Positivity from a second-order differential inequality and zero initial data. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Pang

noncomputable section

theorem positive_of_positive_derivative_of_initial_nonneg {f g : ℝ → ℝ}
    (hf : ∀ x : ℝ, HasDerivAt f (g x) x) (hf0 : 0 ≤ f 0)
    (hpos : ∀ x : ℝ, 0 < x → 0 < g x) {t : ℝ} (ht : 0 < t) : 0 < f t := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f y - f 0) (g x) x :=
    fun x => (hf x).sub_const _
  have h := positive_of_positive_derivative hd (sub_self _) hpos ht
  linarith

theorem positive_of_second_order_operator_of_nonneg_deriv {f g h : ℝ → ℝ} (a : ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (g x) x)
    (hg : ∀ x : ℝ, HasDerivAt g (h x) x)
    (hf0 : f 0 = 0) (hg0 : 0 ≤ g 0)
    (hop : ∀ x : ℝ, 0 < x → 0 < h x - a ^ 2 * f x)
    {t : ℝ} (ht : 0 < t) : 0 < f t := by
  have hu : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (a * y) * (g y - a * f y))
        (Real.exp (a * x) * (h x - a ^ 2 * f x)) x := by
    intro x
    have hd := (((hasDerivAt_id x).const_mul a).exp).mul
      ((hg x).sub ((hf x).const_mul a))
    apply hd.congr_deriv
    simp only [id_eq, Pi.sub_apply]
    ring
  have hup : ∀ x : ℝ, 0 < x → 0 < g x - a * f x := by
    intro x hx
    have hp : 0 < Real.exp (a * x) * (g x - a * f x) :=
      positive_of_positive_derivative_of_initial_nonneg hu
        (by simpa only [hf0, mul_zero, sub_zero, Real.exp_zero, one_mul] using hg0)
        (fun y hy => mul_pos (Real.exp_pos _) (hop y hy)) hx
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hp
  have hv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (-a * y) * f y)
        (Real.exp (-a * x) * (g x - a * f x)) x := by
    intro x
    have hd := (((hasDerivAt_id x).const_mul (-a)).exp).mul (hf x)
    apply hd.congr_deriv
    simp only [id_eq]
    ring
  have hvp : 0 < Real.exp (-a * t) * f t :=
    positive_of_positive_derivative hv (by simp only [hf0, mul_zero])
      (fun x hx => mul_pos (Real.exp_pos _) (hup x hx)) ht
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hvp

theorem positive_of_second_order_operator {f g h : ℝ → ℝ} (a : ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (g x) x)
    (hg : ∀ x : ℝ, HasDerivAt g (h x) x)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hop : ∀ x : ℝ, 0 < x → 0 < h x - a ^ 2 * f x)
    {t : ℝ} (ht : 0 < t) : 0 < f t :=
  positive_of_second_order_operator_of_nonneg_deriv a hf hg hf0
    (by rw [hg0]) hop ht

end
end ENT.Pang
