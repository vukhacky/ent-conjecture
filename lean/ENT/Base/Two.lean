module

public import ENT.Base.TwoEntropy
public import ENT.Base.TwoScalar
public import ENT.Basic.Coefficients
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
The complete two-dimensional ENT statement.  Zero coefficients use the scaled
uniform density; the other coefficients use the proved convolution density.
Signs and ordering are handled by equalities of the canonical laws.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory

namespace ENT

noncomputable section

def nonnegTwoFiniteEntropyDensity (a : Fin 2 → ℝ) (ha : 0 < a 0) (hb : 0 ≤ a 1) :
    FiniteEntropyDensity (projectionLaw a) :=
  if hzero : a 1 = 0 then
    (scaledUniformFiniteEntropyDensity (a 0) ha).transport
      (projectionLaw_two_of_zero_right a hzero).symm
  else
    twoFiniteEntropyDensity a ha (lt_of_le_of_ne hb (Ne.symm hzero))

theorem nonnegTwoFiniteEntropyDensity_entropy (a : Fin 2 → ℝ) (ha : 0 < a 0)
    (hb : 0 ≤ a 1) (hab : a 1 ≤ a 0) :
    (nonnegTwoFiniteEntropyDensity a ha hb).entropy =
      Real.log (2 * a 0) + a 1 / (2 * a 0) := by
  by_cases hzero : a 1 = 0
  · simp [nonnegTwoFiniteEntropyDensity, hzero]
  · simp only [nonnegTwoFiniteEntropyDensity, dite_eq_right hzero]
    exact twoFiniteEntropyDensity_entropy a ha (lt_of_le_of_ne hb (Ne.symm hzero)) hab

theorem ent_two_ordered (a : Fin 2 → ℝ) (ha : IsUnit a) (h0 : 0 < a 0)
    (h1 : 0 ≤ a 1) (horder : a 1 ≤ a 0) :
    ∃ p : FiniteEntropyDensity (projectionLaw a),
    ∃ q : FiniteEntropyDensity (projectionLaw (diagonal 2)),
      p.entropy ≤ q.entropy ∧ (p.entropy = q.entropy ↔ IsDiagonal a) := by
  let p := nonnegTwoFiniteEntropyDensity a h0 h1
  have hdpos : 0 < diagonal 2 0 := by
    unfold diagonal
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  let q := nonnegTwoFiniteEntropyDensity (diagonal 2) hdpos hdpos.le
  have hsum : (a 0) ^ 2 + (a 1) ^ 2 = 1 := by
    simpa only [IsUnit, Fin.sum_univ_two] using ha
  have hdsum : (diagonal 2 0) ^ 2 + (diagonal 2 1) ^ 2 = 1 := by
    simpa only [IsUnit, Fin.sum_univ_two] using (isUnit_diagonal (n := 2) (by decide))
  have hp : p.entropy = twoEntropyModel (a 1 / a 0) := by
    rw [nonnegTwoFiniteEntropyDensity_entropy a h0 h1 horder]
    exact normalized_trapezoid_entropy h0 hsum
  have hq : q.entropy = twoEntropyModel 1 := by
    rw [nonnegTwoFiniteEntropyDensity_entropy (diagonal 2) hdpos hdpos.le le_rfl]
    rw [normalized_trapezoid_entropy hdpos hdsum]
    have hratio : diagonal 2 1 / diagonal 2 0 = 1 := div_self hdpos.ne'
    rw [hratio]
  have hr0 : 0 ≤ a 1 / a 0 := div_nonneg h1 h0.le
  have hr1 : a 1 / a 0 ≤ 1 := (div_le_one h0).mpr horder
  refine ⟨p, q, ?_, ?_⟩
  · rw [hp, hq]
    exact twoEntropyModel_le hr0 hr1
  · rw [hp, hq, twoEntropyModel_eq_iff hr0 hr1, div_eq_one_iff_eq h0.ne',
      isDiagonal_two_iff_eq_of_nonneg ha h0.le h1]
    exact eq_comm

theorem ent_two : ENTAt 2 := by
  intro a ha
  let b : Fin 2 → ℝ := fun i => |a i|
  have hb : IsUnit b := (isUnit_abs_iff a).mpr ha
  have hbn : ∀ i, 0 ≤ b i := fun i => abs_nonneg (a i)
  rcases le_total (b 1) (b 0) with horder | horder
  · have hb0 : 0 < b 0 := first_pos_of_isUnit_nonneg_ordered hb (hbn 0) (hbn 1) horder
    obtain ⟨p, q, hle, heq⟩ := ent_two_ordered b hb hb0 (hbn 1) horder
    refine ⟨p.transport (projectionLaw_abs a), q, ?_, ?_⟩
    · simpa only [FiniteEntropyDensity.entropy_transport] using hle
    · simpa only [FiniteEntropyDensity.entropy_transport] using
        heq.trans (isDiagonal_abs_iff a)
  · let c : Fin 2 → ℝ := fun i => b i.rev
    have hc : IsUnit c := (isUnit_two_swap_iff b).mpr hb
    have hcn : ∀ i, 0 ≤ c i := fun i => hbn i.rev
    have hcorder : c 1 ≤ c 0 := by
      simpa only [c, show (0 : Fin 2).rev = 1 by decide,
        show (1 : Fin 2).rev = 0 by decide] using horder
    have hc0 : 0 < c 0 := first_pos_of_isUnit_nonneg_ordered hc (hcn 0) (hcn 1) hcorder
    obtain ⟨p, q, hle, heq⟩ := ent_two_ordered c hc hc0 (hcn 1) hcorder
    have hlaw : projectionLaw c = projectionLaw a :=
      (projectionLaw_two_swap b).trans (projectionLaw_abs a)
    have hdiag : IsDiagonal c ↔ IsDiagonal a :=
      (isDiagonal_two_swap_iff b).trans (isDiagonal_abs_iff a)
    refine ⟨p.transport hlaw, q, ?_, ?_⟩
    · simpa only [FiniteEntropyDensity.entropy_transport] using hle
    · simpa only [FiniteEntropyDensity.entropy_transport] using heq.trans hdiag

end
end ENT
