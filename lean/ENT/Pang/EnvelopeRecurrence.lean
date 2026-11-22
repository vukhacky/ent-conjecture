module

public import ENT.Pang.EnvelopeMass

/-!
# Even-moment recurrence for the envelope

For convenience the checked recurrence assumes `2*k+5<n`, one unit stronger
than the sharp convergence endpoint. This includes every moment used at
`n≥150`. Integrability of the primitive and its derivative makes both boundary
terms vanish through mathlib's improper-integral theorem.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory

namespace ENT.Pang

noncomputable section

theorem shifted_envelope_eq {n : ℕ} (hn : 0 < n) (u : ℝ) :
    (1 + u ^ 2 / (n : ℝ)) ^ (-((n : ℝ) - 3) / 2) =
      (1 + u ^ 2 / (n : ℝ)) * pangEnvelope n u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < 1 + u ^ 2 / (n : ℝ) := by positivity
  have he : -((n : ℝ) - 3) / 2 = 1 + (-((n : ℝ) - 1) / 2) := by ring
  rw [he, Real.rpow_add hb, Real.rpow_one]
  rfl

def envelopeMomentPrimitive (n k : ℕ) (u : ℝ) : ℝ :=
  u ^ (2 * k + 1) * (1 + u ^ 2 / (n : ℝ)) ^ (-((n : ℝ) - 3) / 2)

theorem envelopeMomentPrimitive_eq {n : ℕ} (hn : 0 < n) (k : ℕ) (u : ℝ) :
    envelopeMomentPrimitive n k u =
      u ^ (2 * k + 1) * pangEnvelope n u +
        (1 / (n : ℝ)) * (u ^ (2 * k + 3) * pangEnvelope n u) := by
  unfold envelopeMomentPrimitive
  rw [shifted_envelope_eq hn]
  simp only [pow_add]
  ring

theorem integrable_envelopeMomentPrimitive {n k : ℕ} (hn : 2 * k + 5 < n) :
    Integrable (envelopeMomentPrimitive n k) := by
  have h1 := integrable_pow_mul_pangEnvelope (n := n) (k := 2 * k + 1) (by omega)
  have h3 := integrable_pow_mul_pangEnvelope (n := n) (k := 2 * k + 3) (by omega)
  have h := h1.add (h3.const_mul (1 / (n : ℝ)))
  apply h.congr
  exact Filter.Eventually.of_forall (fun u => (envelopeMomentPrimitive_eq (by omega) k u).symm)

theorem hasDerivAt_envelopeMomentPrimitive {n : ℕ} (hn : 0 < n) (k : ℕ) (u : ℝ) :
    HasDerivAt (envelopeMomentPrimitive n k)
      (((2 * k + 1 : ℕ) : ℝ) * (u ^ (2 * k) * pangEnvelope n u) -
        ((n : ℝ) - 2 * (k : ℝ) - 4) / (n : ℝ) *
          (u ^ (2 * (k + 1)) * pangEnvelope n u)) u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < 1 + u ^ 2 / (n : ℝ) := by positivity
  have h := ((hasDerivAt_id u).pow (2 * k + 1)).mul
    (((hasDerivAt_const u (1 : ℝ)).add (((hasDerivAt_id u).pow 2).div_const (n : ℝ))).rpow_const
      (p := -((n : ℝ) - 3) / 2) (Or.inl hb.ne'))
  apply h.congr_deriv
  simp only [Pi.add_apply, Pi.pow_apply, id_eq, Nat.reduceSub, Nat.add_sub_cancel,
    pow_one, Nat.cast_ofNat, zero_add, mul_one]
  have he : -((n : ℝ) - 3) / 2 - 1 = -((n : ℝ) - 1) / 2 := by ring
  rw [he, shifted_envelope_eq hn]
  change ((2 * k + 1 : ℕ) : ℝ) * u ^ (2 * k) *
      ((1 + u ^ 2 / (n : ℝ)) * pangEnvelope n u) +
    u ^ (2 * k + 1) * (2 * u / (n : ℝ) * (-((n : ℝ) - 3) / 2) * pangEnvelope n u) = _
  rw [show 2 * (k + 1) = 2 * k + 2 by omega]
  simp only [pow_add, pow_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp [hnR.ne']
  ring

theorem envelopeMoment_succ {n k : ℕ} (hn : 2 * k + 5 < n) :
    envelopeMoment n (k + 1) =
      ((2 * k + 1 : ℕ) : ℝ) * (n : ℝ) / ((n : ℝ) - 2 * (k : ℝ) - 4) *
        envelopeMoment n k := by
  have hnR : 2 * (k : ℝ) + 5 < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hd : (n : ℝ) - 2 * (k : ℝ) - 4 ≠ 0 := by linarith
  have h0 := integrable_pow_mul_pangEnvelope (n := n) (k := 2 * k) (by omega)
  have h1 := integrable_pow_mul_pangEnvelope (n := n) (k := 2 * (k + 1)) (by omega)
  have hi : Integrable (fun u : ℝ => ((2 * k + 1 : ℕ) : ℝ) *
      (u ^ (2 * k) * pangEnvelope n u) -
        ((n : ℝ) - 2 * (k : ℝ) - 4) / (n : ℝ) *
          (u ^ (2 * (k + 1)) * pangEnvelope n u)) :=
    (h0.const_mul _).sub (h1.const_mul _)
  have h := integral_eq_zero_of_hasDerivAt_of_integrable
    (hasDerivAt_envelopeMomentPrimitive (by omega : 0 < n) k) hi
    (integrable_envelopeMomentPrimitive hn)
  rw [integral_sub (h0.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul] at h
  have he : (∫ u : ℝ, u ^ (2 * (k + 1)) * pangEnvelope n u) =
      ((2 * k + 1 : ℕ) : ℝ) * (n : ℝ) / ((n : ℝ) - 2 * (k : ℝ) - 4) *
        ∫ u : ℝ, u ^ (2 * k) * pangEnvelope n u := by
    field_simp [hd]
    field_simp [hn0] at h
    nlinarith
  unfold envelopeMoment
  rw [he]
  ring

end
end ENT.Pang
