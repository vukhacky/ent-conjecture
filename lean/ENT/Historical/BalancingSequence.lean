module

public import ENT.Comparison.GlobalBalancing
public import ENT.Comparison.GenericContraction
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Analysis.SpecificLimits.Basic

/-! The prescribed largest-smallest balancing iteration. Squared coefficients
remain in the simplex and their deficit contracts geometrically. Convergence
of actual bounded-continuous expectations follows from dominated convergence,
as packaged by `continuous_weightExpectation`. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace ENT.Comparison
noncomputable section

theorem exists_maxWeightIndex {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) :
    ∃ i : Fin n, ∀ k, w k ≤ w i := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finite.exists_max w

theorem exists_minWeightIndex {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) :
    ∃ i : Fin n, ∀ k, w i ≤ w k := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finite.exists_min w

def maxWeightIndex {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) : Fin n :=
  Classical.choose (exists_maxWeightIndex hn w)

def minWeightIndex {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) : Fin n :=
  Classical.choose (exists_minWeightIndex hn w)

theorem le_maxWeightIndex {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) (k : Fin n) :
    w k ≤ w (maxWeightIndex hn w) :=
  Classical.choose_spec (exists_maxWeightIndex hn w) k

theorem minWeightIndex_le {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) (k : Fin n) :
    w (minWeightIndex hn w) ≤ w k :=
  Classical.choose_spec (exists_minWeightIndex hn w) k

theorem balanceWeights_self {n : ℕ} (w : Fin n → ℝ) (i : Fin n) :
    balanceWeights w i i = w := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [balanceWeights]
  · simp only [balanceWeights, if_neg hk]

def extremeBalance {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) : Fin n → ℝ :=
  balanceWeights w (maxWeightIndex hn w) (minWeightIndex hn w)

theorem extremes_eq_implies_flat {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ)
    (hsum : ∑ k, w k = 1) (heq : maxWeightIndex hn w = minWeightIndex hn w) :
    w = flatWeights n := by
  have hc := reciprocal_mem_weight_range hn w hsum
    (w (minWeightIndex hn w)) (w (maxWeightIndex hn w))
    (fun k => ⟨minWeightIndex_le hn w k, le_maxWeightIndex hn w k⟩)
  funext k
  have hmin := minWeightIndex_le hn w k
  have hmax := le_maxWeightIndex hn w k
  rw [heq] at hc hmax
  change w k = (n : ℝ)⁻¹
  linarith [hc.1, hc.2]

theorem extremeBalance_mem_weightSimplex {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw : w ∈ weightSimplex n) :
    extremeBalance hn w ∈ weightSimplex n := by
  by_cases hij : maxWeightIndex hn w = minWeightIndex hn w
  · simpa only [extremeBalance, hij, balanceWeights_self] using hw
  · exact balanceWeights_mem_weightSimplex hw _ _ hij

theorem extremeBalance_energy_contracts {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) :
    weightEnergy (extremeBalance hn w) (n : ℝ)⁻¹ ≤
      (1 - 1 / (2 * (n : ℝ))) * weightEnergy w (n : ℝ)⁻¹ := by
  by_cases hij : maxWeightIndex hn w = minWeightIndex hn w
  · have hflat := extremes_eq_implies_flat hn w hw.2 hij
    rw [extremeBalance, hij, balanceWeights_self, hflat]
    simp [weightEnergy, flatWeights]
  · exact weightEnergy_balance_extremes hn w hw.2 _ _ hij
      (fun k => ⟨minWeightIndex_le hn w k, le_maxWeightIndex hn w k⟩)

def balancingSequence {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => w
  | m + 1 => extremeBalance hn (balancingSequence hn w m)

theorem balancingSequence_mem {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw : w ∈ weightSimplex n) (m : ℕ) :
    balancingSequence hn w m ∈ weightSimplex n := by
  induction m with
  | zero => exact hw
  | succ m ih => exact extremeBalance_mem_weightSimplex hn ih

theorem balancingFactor_mem {n : ℕ} (hn : 0 < n) :
    (1 - 1 / (2 * (n : ℝ))) ∈ Ico (0 : ℝ) 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have hlo : 1 / (2 * (n : ℝ)) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hhi : 0 < 1 / (2 * (n : ℝ)) := by positivity
  exact ⟨by linarith, by linarith⟩

theorem balancingSequence_energy_bound {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw : w ∈ weightSimplex n) (m : ℕ) :
    weightEnergy (balancingSequence hn w m) (n : ℝ)⁻¹ ≤
      (1 - 1 / (2 * (n : ℝ))) ^ m * weightEnergy w (n : ℝ)⁻¹ := by
  exact geometric_energy_bound
    (fun m => weightEnergy (balancingSequence hn w m) (n : ℝ)⁻¹)
    _ (balancingFactor_mem hn).1
    (fun m => extremeBalance_energy_contracts hn _ (balancingSequence_mem hn hw m)) m

theorem balancingSequence_energy_tendsto {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw : w ∈ weightSimplex n) :
    Tendsto (fun m => weightEnergy (balancingSequence hn w m) (n : ℝ)⁻¹) atTop (𝓝 0) := by
  apply squeeze_zero (fun m => weightEnergy_nonneg _ _) (balancingSequence_energy_bound hn hw)
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (balancingFactor_mem hn).1 (balancingFactor_mem hn).2).mul_const (weightEnergy w (n : ℝ)⁻¹)
  simpa only [zero_mul] using h

theorem balancingSequence_coord_tendsto {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw : w ∈ weightSimplex n) (i : Fin n) :
    Tendsto (fun m => balancingSequence hn w m i) atTop (𝓝 ((n : ℝ)⁻¹)) := by
  have hsquare : Tendsto (fun m => (balancingSequence hn w m i - (n : ℝ)⁻¹) ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun m => sq_nonneg _) _ (balancingSequence_energy_tendsto hn hw)
    intro m
    change (balancingSequence hn w m i - (n : ℝ)⁻¹) ^ 2 ≤
      ∑ j : Fin n, (balancingSequence hn w m j - (n : ℝ)⁻¹) ^ 2
    exact Finset.single_le_sum
      (f := fun j : Fin n => (balancingSequence hn w m j - (n : ℝ)⁻¹) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have habs : Tendsto (fun m => |balancingSequence hn w m i - (n : ℝ)⁻¹|) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  have hdiff : Tendsto (fun m => balancingSequence hn w m i - (n : ℝ)⁻¹) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const ((n : ℝ)⁻¹)

theorem balancingSequence_tendsto {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw : w ∈ weightSimplex n) :
    Tendsto (balancingSequence hn w) atTop (𝓝 (flatWeights n)) :=
  tendsto_pi_nhds.mpr (balancingSequence_coord_tendsto hn hw)

theorem balancingSequence_coefficients_tendsto {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw : w ∈ weightSimplex n) :
    Tendsto (fun m i => Real.sqrt (balancingSequence hn w m i)) atTop (𝓝 (diagonal n)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (balancingSequence_coord_tendsto hn hw i)
  simpa only [Function.comp_def, Real.sqrt_inv, diagonal] using h

theorem balancingSequence_expectation_tendsto {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw : w ∈ weightSimplex n)
    {V : ℝ → ℝ} (hV : Continuous V) {C : ℝ} (hC : ∀ x, ‖V x‖ ≤ C) :
    Tendsto (fun m => weightExpectation V (balancingSequence hn w m)) atTop
      (𝓝 (weightExpectation V (flatWeights n))) :=
  (continuous_weightExpectation hV hC).continuousAt.tendsto.comp
    (balancingSequence_tendsto hn hw)

end
end ENT.Comparison
