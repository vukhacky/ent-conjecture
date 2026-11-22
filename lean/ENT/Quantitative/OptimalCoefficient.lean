module

public import ENT.Quantitative.SharpnessCoefficients
public import ENT.Quantitative.StabilityDefinitions
public import ENT.AllDimensions
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! The optimal dimension-dependent linear stability coefficient is an
infimum over genuine normalized projection entropy gaps. Nonemptiness and a
lower bound are proved for every dimension at least two. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace ENT.Quantitative
noncomputable section

def normalizedEntropySlope {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) : ℝ :=
  (n : ℝ) * (diagonalEntropy n - projectionEntropy a ha) / deficit a

def entropySlopeSet (n : ℕ) : Set ℝ :=
  {c | ∃ (a : Fin n → ℝ) (ha : IsUnit a),
    0 < deficit a ∧ c = normalizedEntropySlope a ha}

/-- The infimum is used only in dimensions `n ≥ 2`, where the admissible set
is nonempty and bounded below. Those facts are proved below, not assumed. -/
def optimalCoefficient (n : ℕ) : ℝ := sInf (entropySlopeSet n)

theorem entropySlopeSet_nonempty_succ {m : ℕ} (hm : 0 < m) :
    (entropySlopeSet (m + 1)).Nonempty := by
  exact ⟨_, oneZeroCoefficients m, oneZeroCoefficients_isUnit hm,
    oneZeroCoefficients_deficit_pos hm, rfl⟩

theorem entropySlopeSet_nonempty {n : ℕ} (hn : 2 ≤ n) :
    (entropySlopeSet n).Nonempty := by
  cases n with
  | zero => omega
  | succ m => exact entropySlopeSet_nonempty_succ (by omega)

theorem projectionEntropy_le_diagonalEntropy {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    projectionEntropy a ha ≤ diagonalEntropy n := by
  let p := projectionFiniteEntropyDensity a ha
  let q := projectionFiniteEntropyDensity (diagonal n) (isUnit_diagonal hn)
  rw [projectionEntropy_eq a ha p, diagonalEntropy_eq hn q]
  exact (ent_conjecture_for_densities hn a ha p q).1

theorem normalizedEntropySlope_nonneg {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    0 ≤ normalizedEntropySlope a ha := by
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg n)
      (sub_nonneg.mpr (projectionEntropy_le_diagonalEntropy hn a ha)))
    (deficit_nonneg a)

theorem entropySlopeSet_bddBelow {n : ℕ} (hn : 0 < n) :
    BddBelow (entropySlopeSet n) := by
  refine ⟨0, ?_⟩
  rintro c ⟨a, ha, hδ, rfl⟩
  exact normalizedEntropySlope_nonneg hn a ha

theorem optimalCoefficient_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ optimalCoefficient n := by
  apply le_csInf (entropySlopeSet_nonempty hn)
  rintro c ⟨a, ha, hδ, rfl⟩
  exact normalizedEntropySlope_nonneg (by omega) a ha

theorem optimalCoefficient_le_slope {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : IsUnit a) (hδ : 0 < deficit a) :
    optimalCoefficient n ≤ normalizedEntropySlope a ha := by
  exact csInf_le (entropySlopeSet_bddBelow hn) ⟨a, ha, hδ, rfl⟩

theorem optimalCoefficient_le_adjacent_entropy_gap {m : ℕ} (hm : 0 < m) :
    optimalCoefficient (m + 1) ≤
      (m + 1 : ℝ)^2 * (m : ℝ) * (diagonalEntropy (m + 1) - diagonalEntropy m) := by
  have h := optimalCoefficient_le_slope (by omega) (oneZeroCoefficients m)
    (oneZeroCoefficients_isUnit hm) (oneZeroCoefficients_deficit_pos hm)
  simpa only [normalizedEntropySlope, Nat.cast_add, Nat.cast_one,
    oneZeroCoefficients_normalized_gap hm] using h

theorem optimalCoefficient_lower_of_stability {n : ℕ} (hn : 2 ≤ n) {β : ℝ}
    (h : EntropyStabilityAt n β) :
    (n : ℝ) * β ≤ optimalCoefficient n := by
  apply le_csInf (entropySlopeSet_nonempty hn)
  rintro c ⟨a, ha, hδ, rfl⟩
  obtain ⟨p, q, hgap⟩ := h a ha
  rw [← projectionEntropy_eq a ha p, ← diagonalEntropy_eq (by omega) q] at hgap
  apply (le_div_iff₀ hδ).mpr
  calc
    (n : ℝ) * β * deficit a = (n : ℝ) * (β * deficit a) := by ring
    _ ≤ (n : ℝ) * (diagonalEntropy n - projectionEntropy a ha) :=
      mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg n)

theorem optimalCoefficient_lower_of_kl_stability {n : ℕ} (hn : 2 ≤ n) {β : ℝ}
    (h : KLStabilityAt n β) :
    (n : ℝ) * β ≤ optimalCoefficient n :=
  optimalCoefficient_lower_of_stability hn h.entropyStabilityAt

end
end ENT.Quantitative
