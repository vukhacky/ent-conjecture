module

public import ENT.Historical.CappedDisintegrationTwo
public import Mathlib.Analysis.Convex.Continuous

/-! Conditional coordinate laws for uniform cubes in every dimension n ≥ 2, for arbitrary coordinate indices and convex tests. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace ENT.Historical
noncomputable section
open Spline

def cubeCoordinateDensity (n : ℕ) (s : ℝ) : ℝ → ℝ :=
  if n = 2 then twoCappedMarginalDensity s else cappedMarginalDensity n s

def cubeCoordinateKernel (n : ℕ) : Kernel ℝ ℝ :=
  if n = 2 then twoCappedMarginalKernel else cappedMarginalKernel n

theorem cubeCoordinateKernel_markov (n : ℕ) (hn : 2 ≤ n) :
    IsMarkovKernel (cubeCoordinateKernel n) := by
  by_cases hn2 : n = 2
  · simp only [cubeCoordinateKernel, if_pos hn2]
    infer_instance
  · simpa only [cubeCoordinateKernel, if_neg hn2] using cappedMarginalKernel_markov n (by omega)

theorem cubeCoordinateKernel_apply_interior (n : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) n) :
    cubeCoordinateKernel n s = volume.withDensity (fun x => ENNReal.ofReal (cubeCoordinateDensity n s x)) := by
  by_cases hn2 : n = 2
  · subst n
    simpa only [cubeCoordinateKernel, cubeCoordinateDensity, if_pos rfl, ite_true] using
      twoCappedMarginalKernel_apply_interior (by simpa only [Nat.cast_ofNat] using hs)
  · simpa only [cubeCoordinateKernel, cubeCoordinateDensity, if_neg hn2] using
      cappedMarginalKernel_apply_interior n hs

theorem sumCoordinateLaw_eq {n : ℕ} (i j : Fin n) :
    (unitCube01 n).map (fun x => (sumProjection01 n x, x i)) =
      (unitCube01 n).map (fun x => (sumProjection01 n x, x j)) := by
  let e := coordinatePermutation (Equiv.swap i j)
  have he : MeasurePreserving e (unitCube01 n) (unitCube01 n) :=
    measurePreserving_piCongrLeft (fun _ : Fin n => uniform01) (Equiv.swap i j).symm
  have hfun : (fun x : Fin n → ℝ => (sumProjection01 n x, x j)) =
      (fun x => (sumProjection01 n x, x i)) ∘ e := by
    funext x
    simp only [Function.comp_apply, e, coordinatePermutation_apply, Equiv.swap_apply_left]
    congr 1
    simp only [sumProjection01, coordinatePermutation_apply]
    exact (Equiv.sum_comp (Equiv.swap i j) x).symm
  rw [hfun, ← Measure.map_map (by fun_prop) he.measurable, he.map_eq]

theorem cubeCoordinateKernel_disintegration (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    (unitCube01 n).map (fun x => (sumProjection01 n x, x i)) =
      sumLaw01 n ⊗ₘ cubeCoordinateKernel n := by
  let i₀ : Fin n := ⟨0, by omega⟩
  rw [sumCoordinateLaw_eq i i₀]
  by_cases hn2 : n = 2
  · subst n
    have hi₀ : i₀ = (0 : Fin 2) := by apply Fin.ext; rfl
    rw [hi₀]
    simpa only [cubeCoordinateKernel, if_pos rfl, ite_true] using twoCappedMarginalKernel_disintegration
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hi₀ : i₀ = (0 : Fin (m + 1)) := by apply Fin.ext; rfl
    rw [hi₀]
    simpa only [cubeCoordinateKernel, if_neg hn2, Nat.succ_eq_add_one] using
      cappedMarginalKernel_disintegration m (by omega)

theorem cubeCoordinateDensity_nonneg (n : ℕ) (hn : 2 ≤ n) (s x : ℝ) :
    0 ≤ cubeCoordinateDensity n s x := by
  by_cases hn2 : n = 2
  · simpa only [cubeCoordinateDensity, if_pos hn2] using twoCappedMarginalDensity_nonneg s x
  · simpa only [cubeCoordinateDensity, if_neg hn2] using cappedMarginalDensity_nonneg n (by omega) s x

theorem measurable_cubeCoordinateDensity (n : ℕ) (s : ℝ) : Measurable (cubeCoordinateDensity n s) := by
  by_cases hn2 : n = 2
  · simp only [cubeCoordinateDensity, if_pos hn2]
    convert measurable_twoCappedMarginalDensity.comp
      (show Measurable (fun x : ℝ => (s, x)) from measurable_const.prodMk measurable_id) using 1
    ext x
    rfl
  · simp only [cubeCoordinateDensity, if_neg hn2]
    convert (measurable_cappedMarginalDensity n).comp
      (show Measurable (fun x : ℝ => (s, x)) from measurable_const.prodMk measurable_id) using 1
    ext x
    rfl

theorem cubeCoordinateDensity_test_integrable (n : ℕ) (hn : 2 ≤ n) (s : ℝ)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 s)) :
    Integrable (fun x => φ x * cubeCoordinateDensity n s x) volume := by
  by_cases hn2 : n = 2
  · simpa only [cubeCoordinateDensity, if_pos hn2] using twoCappedMarginalDensity_test_integrable s hφ
  · simpa only [cubeCoordinateDensity, if_neg hn2] using cappedMarginalDensity_test_integrable n (by omega) s hφ

theorem cubeCoordinateKernel_test_integrable (n : ℕ) (hn : 2 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 s)) :
    Integrable φ (cubeCoordinateKernel n s) := by
  rw [cubeCoordinateKernel_apply_interior n hs,
    integrable_withDensity_iff_integrable_smul'
      (measurable_cubeCoordinateDensity n s).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (cubeCoordinateDensity_nonneg n hn s _), smul_eq_mul,
    mul_comm] using cubeCoordinateDensity_test_integrable n hn s hφ

theorem cubeCoordinateKernel_integral_test (n : ℕ) (hn : 2 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) (φ : ℝ → ℝ) :
    (∫ x, φ x ∂cubeCoordinateKernel n s) = ∫ x, φ x * cubeCoordinateDensity n s x := by
  rw [cubeCoordinateKernel_apply_interior n hs,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_cubeCoordinateDensity n s).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (ENNReal.ofReal (cubeCoordinateDensity n s x)).toReal * φ x = φ x * cubeCoordinateDensity n s x
    rw [ENNReal.toReal_ofReal (cubeCoordinateDensity_nonneg n hn s x), mul_comm]

theorem cubeCoordinateKernel_convexOrder (n : ℕ) (hn : 2 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ (Icc 0 s) φ) (hφcont : ContinuousOn φ (Icc 0 s)) :
    Integrable φ (cubeCoordinateKernel n s) ∧
      (∫ x, φ x ∂cubeCoordinateKernel n s) ≤ ∫ x, φ x * simplexMarginalDensity n s x := by
  refine ⟨cubeCoordinateKernel_test_integrable n hn hs hφcont, ?_⟩
  rw [cubeCoordinateKernel_integral_test n hn hs]
  by_cases hn2 : n = 2
  · subst n
    simpa only [cubeCoordinateDensity, if_pos rfl, ite_true] using
      twoCappedMarginal_convexOrder (by simpa only [Nat.cast_ofNat] using hs) hφ hφcont
  · simpa only [cubeCoordinateDensity, if_neg hn2] using
      cappedMarginal_convexOrder n (by omega) hs hφ hφcont

theorem cubeCoordinateKernel_convexOrder_global (n : ℕ) (hn : 2 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) :
    Integrable φ (cubeCoordinateKernel n s) ∧
      (∫ x, φ x ∂cubeCoordinateKernel n s) ≤ ∫ x, φ x * simplexMarginalDensity n s x := by
  apply cubeCoordinateKernel_convexOrder n hn hs
  · exact hφ.subset (subset_univ _) (convex_Icc _ _)
  · exact (hφ.continuousOn isOpen_univ).mono (subset_univ _)

end
end ENT.Historical
