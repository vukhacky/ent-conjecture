module

public import ENT.Entropy.LawInvariance
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
Gibbs' inequality and the entropy comparison identity for actual finite-entropy
densities.  A finite KL value requires explicit cross-integrability and the
almost-everywhere support condition; no unguarded totalized integral is used as
a substitute for an infinite relative entropy.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ENT

noncomputable section

def gibbsDefect (u v : ℝ) : ℝ :=
  u * Real.log u - u * Real.log v - u + v

private theorem gibbsDefect_eq_ratio {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    gibbsDefect u v = v * ((u / v) * Real.log (u / v) + 1 - u / v) := by
  rw [gibbsDefect, Real.log_div hu hv]
  field_simp [hv]
  ring

theorem gibbsDefect_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hsupport : v = 0 → u = 0) : 0 ≤ gibbsDefect u v := by
  by_cases hv0 : v = 0
  · simp [gibbsDefect, hsupport hv0, hv0]
  by_cases hu0 : u = 0
  · simpa [gibbsDefect, hu0] using hv
  rw [gibbsDefect_eq_ratio hu0 hv0]
  apply mul_nonneg hv
  have h := Real.self_sub_one_le_mul_log (div_nonneg hu hv)
  linarith

theorem gibbsDefect_pos_of_ne {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hsupport : v = 0 → u = 0) (hne : u ≠ v) : 0 < gibbsDefect u v := by
  by_cases hv0 : v = 0
  · exact False.elim (hne ((hsupport hv0).trans hv0.symm))
  have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  by_cases hu0 : u = 0
  · simpa [gibbsDefect, hu0] using hvpos
  rw [gibbsDefect_eq_ratio hu0 hv0]
  apply mul_pos hvpos
  have hrne : u / v ≠ 1 := fun h => hne ((div_eq_one_iff_eq hv0).mp h)
  have h := Real.self_sub_one_lt_mul_log (div_nonneg hu hv) hrne
  linarith

theorem gibbsDefect_eq_zero_iff {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hsupport : v = 0 → u = 0) : gibbsDefect u v = 0 ↔ u = v := by
  constructor
  · intro h
    by_contra hne
    exact (ne_of_gt (gibbsDefect_pos_of_ne hu hv hsupport hne)) h
  · rintro rfl
    simp [gibbsDefect]

/-- The hypotheses that make the real KL integral finite and semantically valid.
The support field allows arbitrary changes on Lebesgue-null sets. -/
structure FiniteKLData {μ ν : Measure ℝ} (p : FiniteEntropyDensity μ)
    (q : FiniteEntropyDensity ν) : Prop where
  cross_integrable : Integrable (fun x => p.density x * Real.log (q.density x)) volume
  support_ae : ∀ᵐ x ∂volume, q.density x = 0 → p.density x = 0

namespace FiniteKLData

variable {μ ν : Measure ℝ} {p : FiniteEntropyDensity μ} {q : FiniteEntropyDensity ν}

def klDivergence (_h : FiniteKLData p q) : ℝ :=
  ∫ x, p.density x * Real.log (p.density x) - p.density x * Real.log (q.density x)

theorem integrable_klIntegrand (h : FiniteKLData p q) :
    Integrable (fun x => p.density x * Real.log (p.density x) -
      p.density x * Real.log (q.density x)) volume :=
  p.entropy_integrable.sub' h.cross_integrable

theorem integrable_gibbsDefect (h : FiniteKLData p q) :
    Integrable (fun x => gibbsDefect (p.density x) (q.density x)) volume := by
  exact ((p.entropy_integrable.sub' h.cross_integrable).sub' p.integrable).fun_add q.integrable

theorem gibbsDefect_nonneg_ae (h : FiniteKLData p q) :
    0 ≤ᵐ[volume] (fun x => gibbsDefect (p.density x) (q.density x)) := by
  filter_upwards [h.support_ae] with x hx
  exact ENT.gibbsDefect_nonneg (p.nonneg x) (q.nonneg x) hx

theorem integral_gibbsDefect_eq (h : FiniteKLData p q) :
    (∫ x, gibbsDefect (p.density x) (q.density x)) = h.klDivergence := by
  unfold gibbsDefect klDivergence
  rw [integral_add ((p.entropy_integrable.sub' h.cross_integrable).sub' p.integrable) q.integrable,
    integral_sub (p.entropy_integrable.sub' h.cross_integrable) p.integrable,
    p.mass_one, q.mass_one]
  ring

theorem klDivergence_nonneg (h : FiniteKLData p q) : 0 ≤ h.klDivergence := by
  rw [← h.integral_gibbsDefect_eq]
  exact integral_nonneg_of_ae h.gibbsDefect_nonneg_ae

theorem klIntegrand_ae_eq_log_ratio (h : FiniteKLData p q) :
    (fun x => p.density x * Real.log (p.density x) -
      p.density x * Real.log (q.density x)) =ᵐ[volume]
      (fun x => p.density x * Real.log (p.density x / q.density x)) := by
  filter_upwards [h.support_ae] with x hx
  by_cases hp0 : p.density x = 0
  · simp [hp0]
  have hq0 : q.density x ≠ 0 := fun hq0 => hp0 (hx hq0)
  rw [Real.log_div hp0 hq0]
  ring

theorem integrable_log_ratio (h : FiniteKLData p q) :
    Integrable (fun x => p.density x * Real.log (p.density x / q.density x)) volume :=
  h.integrable_klIntegrand.congr h.klIntegrand_ae_eq_log_ratio

theorem klDivergence_eq_log_ratio (h : FiniteKLData p q) :
    h.klDivergence = ∫ x, p.density x * Real.log (p.density x / q.density x) :=
  integral_congr_ae h.klIntegrand_ae_eq_log_ratio

theorem klDivergence_eq_zero_iff_density_ae (h : FiniteKLData p q) :
    h.klDivergence = 0 ↔ p.density =ᵐ[volume] q.density := by
  have hi := integral_eq_zero_iff_of_nonneg_ae h.gibbsDefect_nonneg_ae h.integrable_gibbsDefect
  rw [h.integral_gibbsDefect_eq] at hi
  constructor
  · intro hz
    have hzero := hi.mp hz
    filter_upwards [hzero, h.support_ae] with x hx hs
    exact (ENT.gibbsDefect_eq_zero_iff (p.nonneg x) (q.nonneg x) hs).mp hx
  · intro heq
    apply hi.mpr
    filter_upwards [heq] with x hx
    rw [hx]
    simp [gibbsDefect]

theorem klDivergence_eq_zero_iff (h : FiniteKLData p q) :
    h.klDivergence = 0 ↔ μ = ν := by
  rw [h.klDivergence_eq_zero_iff_density_ae]
  constructor
  · intro hpq
    rw [p.law_eq, q.law_eq]
    exact withDensity_congr_ae (hpq.mono fun x hx => congrArg ENNReal.ofReal hx)
  · intro hμν
    subst ν
    exact p.density_ae_eq q

theorem integrable_potential_gap (h : FiniteKLData p q) :
    Integrable (fun x => (p.density x - q.density x) * Real.log (q.density x)) volume := by
  simpa only [sub_mul] using h.cross_integrable.sub' q.entropy_integrable

theorem entropy_gap_identity (h : FiniteKLData p q) :
    q.entropy - p.entropy =
      (∫ x, (p.density x - q.density x) * Real.log (q.density x)) + h.klDivergence := by
  have hgap : (fun x => (p.density x - q.density x) * Real.log (q.density x)) =
      (fun x => p.density x * Real.log (q.density x) -
        q.density x * Real.log (q.density x)) :=
    funext fun x => sub_mul _ _ _
  rw [hgap, integral_sub h.cross_integrable q.entropy_integrable]
  unfold FiniteEntropyDensity.entropy klDivergence
  rw [integral_sub p.entropy_integrable h.cross_integrable]
  ring

theorem potential_gap_le_entropy_gap (h : FiniteKLData p q) :
    (∫ x, (p.density x - q.density x) * Real.log (q.density x)) ≤
      q.entropy - p.entropy := by
  rw [h.entropy_gap_identity]
  exact le_add_of_nonneg_right h.klDivergence_nonneg

theorem entropy_gap_ge (h : FiniteKLData p q) {c : ℝ}
    (hgap : c ≤ ∫ x, (p.density x - q.density x) * Real.log (q.density x)) :
    c ≤ q.entropy - p.entropy :=
  hgap.trans h.potential_gap_le_entropy_gap

theorem entropy_le (h : FiniteKLData p q)
    (hgap : 0 ≤ ∫ x, (p.density x - q.density x) * Real.log (q.density x)) :
    p.entropy ≤ q.entropy := by
  have hg := h.entropy_gap_ge hgap
  linarith

theorem entropy_eq_iff (h : FiniteKLData p q)
    (hgap : 0 ≤ ∫ x, (p.density x - q.density x) * Real.log (q.density x)) :
    p.entropy = q.entropy ↔ μ = ν := by
  constructor
  · intro heq
    apply h.klDivergence_eq_zero_iff.mp
    have hid := h.entropy_gap_identity
    have hnonneg := h.klDivergence_nonneg
    linarith
  · intro hμν
    subst ν
    exact p.entropy_eq q

theorem entropy_lt_of_law_ne (h : FiniteKLData p q)
    (hgap : 0 ≤ ∫ x, (p.density x - q.density x) * Real.log (q.density x))
    (hne : μ ≠ ν) : p.entropy < q.entropy :=
  lt_of_le_of_ne (h.entropy_le hgap) (fun heq => hne ((h.entropy_eq_iff hgap).mp heq))

end FiniteKLData

end
end ENT
