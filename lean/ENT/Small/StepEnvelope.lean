module

public import ENT.Small.LocalConstants
public import Mathlib.Order.Interval.Set.Union

/-! Assembly of exact, finitely many bounds for the local logarithmic third
derivative.  The singular outer bound is cancelled against the weight before
integrability is proved.  Neither a floating point supremum nor an unverified
quadrature enters this interface. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Small
noncomputable section

theorem stepEnvelope_density_outer (n : ℕ) (hn : 2 ≤ n) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Spline.unitSumSplineDensity n t =
      (Nat.factorial (n - 1) : ℝ)⁻¹ * t ^ (n - 1) := by
  unfold Spline.unitSumSplineDensity
  congr 1
  have h := Spline.unnormalizedSpline_eq_piece n 0 hn (Nat.zero_le n) t ht.1 ht.2
  simpa [Certificate.splinePiece] using h

theorem integral_unitSumSplineDensity_outer (n : ℕ) (hn : 2 ≤ n) (b : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..b, Spline.unitSumSplineDensity n t) =
      b ^ n / ((n : ℝ) * (Nat.factorial (n - 1) : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hf0 : (Nat.factorial (n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  have hd (t : ℝ) : HasDerivAt
      (fun u : ℝ => u ^ n / ((n : ℝ) * (Nat.factorial (n - 1) : ℝ)))
      ((Nat.factorial (n - 1) : ℝ)⁻¹ * t ^ (n - 1)) t := by
    have h := ((hasDerivAt_id t).pow n).div_const
      ((n : ℝ) * (Nat.factorial (n - 1) : ℝ))
    convert h using 1 <;> (try rfl) <;> (try simp only [id_eq, mul_one]) <;>
      field_simp [hn0, hf0] <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => by
      rw [uIcc_of_le hb.1] at ht
      rw [stepEnvelope_density_outer n hn t ⟨ht.1, ht.2.trans hb.2⟩]
      exact hd t)
    ((Spline.continuous_unitSumSplineDensity n).intervalIntegrable 0 b)
  simpa only [zero_pow (by omega : n ≠ 0), zero_div, sub_zero] using hi

theorem integral_unitSumSplineDensity_half (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in (0 : ℝ)..(1 / 2), Spline.unitSumSplineDensity n t) =
      1 / ((n : ℝ) * (Nat.factorial (n - 1) : ℝ) * 2 ^ n) := by
  rw [integral_unitSumSplineDensity_outer n hn (1 / 2) (by norm_num)]
  simp only [div_eq_mul_inv, one_mul, mul_inv_rev, inv_pow]

def stepEnvelopeBound {N : ℕ} (a : ℕ → ℝ) (B : Fin N → ℝ) (C : ℝ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) (1 / 2)).indicator (fun u => C / u ^ 3) t +
    ∑ i : Fin N, (Ioc (a i) (a (i + 1))).indicator (fun _ => B i) t

theorem stepEnvelopeBound_measurable {N : ℕ} (a : ℕ → ℝ) (B : Fin N → ℝ)
    (C : ℝ) : Measurable (stepEnvelopeBound a B C) := by
  unfold stepEnvelopeBound
  apply Measurable.add
  · exact (measurable_const.div (measurable_id.pow_const 3)).indicator measurableSet_Ioc
  · apply Finset.measurable_sum
    intro i hi
    exact measurable_const.indicator measurableSet_Ioc

theorem stepEnvelope_outer_nonneg (C : ℝ) (hC : 0 ≤ C) (t : ℝ) :
    0 ≤ (Ioc (0 : ℝ) (1 / 2)).indicator (fun u => C / u ^ 3) t := by
  by_cases ht : t ∈ Ioc (0 : ℝ) (1 / 2)
  · rw [Set.indicator_of_mem ht]
    exact div_nonneg hC (pow_nonneg ht.1.le 3)
  · simp only [Set.indicator_of_notMem ht, le_refl]

theorem stepEnvelope_cell_nonneg {N : ℕ} (a : ℕ → ℝ) (B : Fin N → ℝ)
    (hB : ∀ i, 0 ≤ B i) (i : Fin N) (t : ℝ) :
    0 ≤ (Ioc (a i) (a (i + 1))).indicator (fun _ => B i) t := by
  by_cases ht : t ∈ Ioc (a i) (a (i + 1))
  · simpa only [Set.indicator_of_mem ht] using hB i
  · simp only [Set.indicator_of_notMem ht, le_refl]

theorem stepEnvelopeBound_nonneg {N : ℕ} (a : ℕ → ℝ) (B : Fin N → ℝ)
    (C : ℝ) (hB : ∀ i, 0 ≤ B i) (hC : 0 ≤ C) (t : ℝ) :
    0 ≤ stepEnvelopeBound a B C t := by
  exact add_nonneg (stepEnvelope_outer_nonneg C hC t)
    (Finset.sum_nonneg fun i hi => stepEnvelope_cell_nonneg a B hB i t)

theorem stepEnvelope_weighted_eq {N : ℕ} (a : ℕ → ℝ) (B : Fin N → ℝ)
    (C : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    f t * t ^ 3 * stepEnvelopeBound a B C t =
      (Ioc (0 : ℝ) (1 / 2)).indicator (fun u => C * f u) t +
        ∑ i : Fin N,
          (Ioc (a i) (a (i + 1))).indicator (fun u => B i * (f u * u ^ 3)) t := by
  unfold stepEnvelopeBound
  rw [mul_add, Finset.mul_sum]
  congr 1
  · by_cases ht : t ∈ Ioc (0 : ℝ) (1 / 2)
    · simp only [Set.indicator_of_mem ht]
      field_simp [ne_of_gt ht.1] <;> ring
    · simp only [Set.indicator_of_notMem ht, mul_zero]
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases ht : t ∈ Ioc (a i) (a (i + 1))
    · simp only [Set.indicator_of_mem ht]
      ring
    · simp only [Set.indicator_of_notMem ht, mul_zero]

theorem integrable_unitSumSplineDensity_mul_cube (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun t => Spline.unitSumSplineDensity n t * t ^ 3) volume := by
  apply ((Spline.continuous_unitSumSplineDensity n).mul (continuous_id.pow 3)).integrable_of_hasCompactSupport
  exact (Spline.hasCompactSupport_unitSumSplineDensity n hn).mul_right

theorem stepEnvelope_weighted_integrable (n : ℕ) (hn : 2 ≤ n) {N : ℕ}
    (a : ℕ → ℝ) (B : Fin N → ℝ) (C : ℝ) :
    Integrable (fun t => Spline.unitSumSplineDensity n t * t ^ 3 *
      stepEnvelopeBound a B C t) volume := by
  simp_rw [stepEnvelope_weighted_eq]
  apply Integrable.add
  · exact ((Spline.integrable_unitSumSplineDensity n hn).const_mul C).indicator measurableSet_Ioc
  · apply integrable_finsetSum
    intro i hi
    exact ((integrable_unitSumSplineDensity_mul_cube n hn).const_mul (B i)).indicator measurableSet_Ioc

theorem stepEnvelopeBound_dominates (n : ℕ) {N : ℕ} (γ : ℝ)
    (hγ : γ ∈ Ico (0 : ℝ) 1) (a : ℕ → ℝ) (B : Fin N → ℝ) (C : ℝ)
    (hstart : a 0 = 1 / 2) (hend : a N = (n : ℝ) / 2)
    (hB : ∀ i, 0 ≤ B i) (hC : 0 ≤ C)
    (houter : ∀ t ∈ Ioc (0 : ℝ) (1 / 2),
      ∀ v ∈ Icc ((1 - γ) * t) (min ((n : ℝ) / 2) ((1 + γ) * t)),
        |logThirdUnitSum n v| ≤ C / t ^ 3)
    (hcell : ∀ i : Fin N,
      ∀ v ∈ Icc ((1 - γ) * a i) (min ((n : ℝ) / 2) ((1 + γ) * a (i + 1))),
        |logThirdUnitSum n v| ≤ B i)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) ((n : ℝ) / 2))
    (v : ℝ) (hv : v ∈ Icc ((1 - γ) * t) (min ((n : ℝ) / 2) ((1 + γ) * t))) :
    |logThirdUnitSum n v| ≤ stepEnvelopeBound a B C t := by
  have hsum : 0 ≤ ∑ i : Fin N,
      (Ioc (a i) (a (i + 1))).indicator (fun _ => B i) t :=
    Finset.sum_nonneg fun i hi => stepEnvelope_cell_nonneg a B hB i t
  by_cases htouter : t ≤ 1 / 2
  · have hmem : t ∈ Ioc (0 : ℝ) (1 / 2) := ⟨ht.1, htouter⟩
    have h := houter t hmem v hv
    unfold stepEnvelopeBound
    rw [Set.indicator_of_mem hmem]
    linarith
  · have hmem : t ∈ Ioc (a 0) (a N) := by
      rw [hstart, hend]
      exact ⟨lt_of_not_ge htouter, ht.2⟩
    have hcover := Ioc_subset_biUnion_Ioc N a hmem
    rcases Set.mem_iUnion.mp hcover with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨hiN, hit⟩
    let j : Fin N := ⟨i, Finset.mem_range.mp hiN⟩
    have hjt : t ∈ Ioc (a j) (a (j + 1)) := hit
    have hminus : 0 ≤ 1 - γ := by linarith [hγ.2]
    have hplus : 0 ≤ 1 + γ := by linarith [hγ.1]
    have hvj : v ∈ Icc ((1 - γ) * a j)
        (min ((n : ℝ) / 2) ((1 + γ) * a (j + 1))) := by
      refine ⟨(mul_le_mul_of_nonneg_left hjt.1.le hminus).trans hv.1, ?_⟩
      exact hv.2.trans (min_le_min_left _ (mul_le_mul_of_nonneg_left hjt.2 hplus))
    have hchosen : B j ≤ ∑ i : Fin N,
        (Ioc (a i) (a (i + 1))).indicator (fun _ => B i) t := by
      have h := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun i : Fin N => (Ioc (a i) (a (i + 1))).indicator (fun _ => B i) t)
        (fun i hi => stepEnvelope_cell_nonneg a B hB i t) (Finset.mem_univ j)
      simpa only [Set.indicator_of_mem hjt] using h
    have hout := stepEnvelope_outer_nonneg C hC t
    have h := hcell j v hvj
    unfold stepEnvelopeBound
    linarith

def stepLogThirdEnvelope (n : ℕ) (hn : 2 ≤ n) {N : ℕ} (γ : ℝ)
    (hγ : γ ∈ Ico (0 : ℝ) 1) (a : ℕ → ℝ) (B : Fin N → ℝ) (C : ℝ)
    (hstart : a 0 = 1 / 2) (hend : a N = (n : ℝ) / 2)
    (hB : ∀ i, 0 ≤ B i) (hC : 0 ≤ C)
    (houter : ∀ t ∈ Ioc (0 : ℝ) (1 / 2),
      ∀ v ∈ Icc ((1 - γ) * t) (min ((n : ℝ) / 2) ((1 + γ) * t)),
        |logThirdUnitSum n v| ≤ C / t ^ 3)
    (hcell : ∀ i : Fin N,
      ∀ v ∈ Icc ((1 - γ) * a i) (min ((n : ℝ) / 2) ((1 + γ) * a (i + 1))),
        |logThirdUnitSum n v| ≤ B i) : LogThirdEnvelope n γ where
  bound := stepEnvelopeBound a B C
  measurable := stepEnvelopeBound_measurable a B C
  nonneg := stepEnvelopeBound_nonneg a B C hB hC
  dominates := stepEnvelopeBound_dominates n γ hγ a B C hstart hend hB hC houter hcell
  weighted_integrable := (stepEnvelope_weighted_integrable n hn a B C).intervalIntegrable

theorem intervalIntegral_indicator_Ioc_inside (f : ℝ → ℝ) {l u a b : ℝ}
    (hla : l ≤ a) (hab : a ≤ b) (hbu : b ≤ u) :
    (∫ t in l..u, (Ioc a b).indicator f t) = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · rw [MeasureTheory.integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le hab]
  · intro t ht
    have hmem : t ∈ Ioc a b := by
      by_contra hnot
      exact ht (Set.indicator_of_notMem hnot f)
    exact ⟨hla.trans_lt hmem.1, hmem.2.trans hbu⟩

theorem averagedRemainderBound_step_eq (n : ℕ) (hn : 2 ≤ n) {N : ℕ}
    (a : ℕ → ℝ) (ha : Monotone a) (B : Fin N → ℝ) (C : ℝ)
    (hstart : a 0 = 1 / 2) (hend : a N = (n : ℝ) / 2) :
    averagedRemainderBound n (stepEnvelopeBound a B C) =
      2 * C * (∫ t in (0 : ℝ)..(1 / 2), Spline.unitSumSplineDensity n t) +
        2 * ∑ i : Fin N, B i *
          (∫ t in a i..a (i + 1), Spline.unitSumSplineDensity n t * t ^ 3) := by
  have hhalf : (1 / 2 : ℝ) ≤ (n : ℝ) / 2 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have houter : IntervalIntegrable
      ((Ioc (0 : ℝ) (1 / 2)).indicator (fun t => C * Spline.unitSumSplineDensity n t))
      volume 0 ((n : ℝ) / 2) :=
    (((Spline.integrable_unitSumSplineDensity n hn).const_mul C).indicator measurableSet_Ioc).intervalIntegrable
  have hcell : ∀ i : Fin N, IntervalIntegrable
      ((Ioc (a i) (a (i + 1))).indicator
        (fun t => B i * (Spline.unitSumSplineDensity n t * t ^ 3)))
      volume 0 ((n : ℝ) / 2) := fun i =>
    (((integrable_unitSumSplineDensity_mul_cube n hn).const_mul (B i)).indicator measurableSet_Ioc).intervalIntegrable
  have hsum : IntervalIntegrable (fun t => ∑ i : Fin N,
      (Ioc (a i) (a (i + 1))).indicator
        (fun t => B i * (Spline.unitSumSplineDensity n t * t ^ 3)) t)
      volume 0 ((n : ℝ) / 2) := by
    exact ⟨integrable_finsetSum Finset.univ (fun i hi => (hcell i).1),
      integrable_finsetSum Finset.univ (fun i hi => (hcell i).2)⟩
  unfold averagedRemainderBound
  simp_rw [stepEnvelope_weighted_eq]
  rw [intervalIntegral.integral_add houter hsum,
    intervalIntegral.integral_finsetSum (fun i hi => hcell i)]
  rw [intervalIntegral_indicator_Ioc_inside _ le_rfl (by norm_num) hhalf,
    intervalIntegral.integral_const_mul]
  have hterms : ∀ i : Fin N,
      (∫ t in (0 : ℝ)..((n : ℝ) / 2), (Ioc (a i) (a (i + 1))).indicator
        (fun t => B i * (Spline.unitSumSplineDensity n t * t ^ 3)) t) =
        B i * (∫ t in a i..a (i + 1), Spline.unitSumSplineDensity n t * t ^ 3) := by
    intro i
    have h0 : (0 : ℝ) ≤ a i := by
      have h := ha (Nat.zero_le (i : ℕ))
      rw [hstart] at h
      linarith
    have h1 : a (i + 1) ≤ (n : ℝ) / 2 := by
      rw [← hend]
      exact ha (Nat.succ_le_of_lt i.isLt)
    rw [intervalIntegral_indicator_Ioc_inside _ h0 (ha (Nat.le_succ _)) h1,
      intervalIntegral.integral_const_mul]
  simp_rw [hterms]
  ring

theorem averagedRemainderBound_step_le (n : ℕ) (hn : 2 ≤ n) {N : ℕ}
    (a : ℕ → ℝ) (ha : Monotone a) (B : Fin N → ℝ) (C : ℝ)
    (hstart : a 0 = 1 / 2) (hend : a N = (n : ℝ) / 2)
    (hB : ∀ i, 0 ≤ B i) (hC : 0 ≤ C) (A₀ : ℝ) (A : Fin N → ℝ)
    (hA₀ : (∫ t in (0 : ℝ)..(1 / 2), Spline.unitSumSplineDensity n t) ≤ A₀)
    (hA : ∀ i : Fin N, (∫ t in a i..a (i + 1),
      Spline.unitSumSplineDensity n t * t ^ 3) ≤ A i) :
    averagedRemainderBound n (stepEnvelopeBound a B C) ≤
      2 * C * A₀ + 2 * ∑ i : Fin N, B i * A i := by
  rw [averagedRemainderBound_step_eq n hn a ha B C hstart hend]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hA₀ (mul_nonneg (by norm_num) hC)
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hA i) (hB i)

end
end ENT.Small
