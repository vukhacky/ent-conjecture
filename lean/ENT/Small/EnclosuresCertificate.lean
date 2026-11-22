module

public import ENT.Small.Enclosures
public import Mathlib.Data.Rat.Cast.Order

/-! A finite rational certificate for an exponential point evaluation. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Small.Enclosures

def ratExpTaylor (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℚ)

def ratExpError (n : ℕ) (r : ℚ) : ℚ :=
  r ^ n * ((n + 1 : ℕ) : ℚ) / ((n.factorial : ℚ) * (n : ℚ))

structure ExpPointCertificate where
  argument : ℚ
  baseLower : ℚ
  baseUpper : ℚ
  lower : ℚ
  upper : ℚ

def ExpPointCertificate.Valid (c : ExpPointCertificate) : Prop :=
  |c.argument / 64| ≤ 1 ∧ 0 ≤ c.baseLower ∧
  c.baseLower ≤ ratExpTaylor 16 (c.argument / 64) - ratExpError 16 1 ∧
  ratExpTaylor 16 (c.argument / 64) + ratExpError 16 1 ≤ c.baseUpper ∧
  c.lower ≤ c.baseLower ^ 64 ∧ c.baseUpper ^ 64 ≤ c.upper

instance (c : ExpPointCertificate) : Decidable c.Valid := by
  unfold ExpPointCertificate.Valid
  infer_instance

noncomputable section

theorem ratExpTaylor_cast (n : ℕ) (x : ℚ) :
    (ratExpTaylor n x : ℝ) = expTaylor n (x : ℝ) := by
  unfold ratExpTaylor expTaylor
  push_cast
  rfl

theorem ratExpError_cast (n : ℕ) (r : ℚ) :
    (ratExpError n r : ℝ) = expError n (r : ℝ) := by
  unfold ratExpError expError
  push_cast
  rfl

theorem ExpPointCertificate.sound (c : ExpPointCertificate) (hc : c.Valid) :
    (c.lower : ℝ) ≤ Real.exp (c.argument : ℝ) ∧
      Real.exp (c.argument : ℝ) ≤ (c.upper : ℝ) := by
  rcases hc with ⟨hx, hl0, hl, hu, hlp, hup⟩
  have hxR : |((c.argument / 64 : ℚ) : ℝ)| ≤ (1 : ℝ) := by exact_mod_cast hx
  have hl0R : (0 : ℝ) ≤ c.baseLower := by exact_mod_cast hl0
  have hlR : (c.baseLower : ℝ) ≤
      expTaylor 16 ((c.argument / 64 : ℚ) : ℝ) - expError 16 1 := by
    have h : (c.baseLower : ℝ) ≤ ((ratExpTaylor 16 (c.argument / 64) - ratExpError 16 1 : ℚ) : ℝ) :=
      by exact_mod_cast hl
    push_cast at h
    simpa only [ratExpTaylor_cast, ratExpError_cast, Rat.cast_one] using h
  have huR : expTaylor 16 ((c.argument / 64 : ℚ) : ℝ) + expError 16 1 ≤
      (c.baseUpper : ℝ) := by
    have h : ((ratExpTaylor 16 (c.argument / 64) + ratExpError 16 1 : ℚ) : ℝ) ≤ (c.baseUpper : ℝ) :=
      by exact_mod_cast hu
    push_cast at h
    simpa only [ratExpTaylor_cast, ratExpError_cast, Rat.cast_one] using h
  have h := exp_enclosure_of_taylor (by norm_num : 0 < (16 : ℕ))
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) hxR hlR huR
  have hp := exp_scale_pow_enclosure hl0R h.1 h.2 64
  have he : (64 : ℝ) * ((c.argument / 64 : ℚ) : ℝ) = (c.argument : ℝ) := by
    push_cast
    ring
  norm_num only [Nat.cast_ofNat] at hp
  rw [he] at hp
  have hlpR : (c.lower : ℝ) ≤ (c.baseLower : ℝ) ^ 64 := by exact_mod_cast hlp
  have hupR : (c.baseUpper : ℝ) ^ 64 ≤ (c.upper : ℝ) := by exact_mod_cast hup
  exact ⟨hlpR.trans hp.1, hp.2.trans hupR⟩

end
end ENT.Small.Enclosures
