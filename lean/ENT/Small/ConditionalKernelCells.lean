module

public import ENT.Small.ConditionalKernelFormula

/-! Exact low-dimensional conditional-variance polynomial certificates.
Every identity below is connected to the actual integral kernel. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Small
noncomputable section
open Spline

def quadraticMonomialPrimitive (m : ℕ) (c u : ℝ) : ℝ :=
  c ^ 2 * (u ^ (m + 1) / (m + 1 : ℕ)) +
    4 * c * (u ^ (m + 2) / (m + 2 : ℕ)) +
    4 * (u ^ (m + 3) / (m + 3 : ℕ))

theorem quadraticPowerPrimitive_of_nonneg (m : ℕ) (c u : ℝ) (hu : 0 ≤ u) :
    quadraticPowerPrimitive m c u = quadraticMonomialPrimitive m c u := by
  simp only [quadraticPowerPrimitive, quadraticMonomialPrimitive, positivePower, max_eq_right hu]

theorem quadraticPowerPrimitive_of_nonpos (m : ℕ) (c u : ℝ) (hu : u ≤ 0) :
    quadraticPowerPrimitive m c u = 0 := by
  simp [quadraticPowerPrimitive, positivePower, max_eq_left hu]

def coordinateSquareKernelPiece (n k : ℕ) (s : ℝ) : ℝ :=
  (Nat.factorial (n - 2) : ℝ)⁻¹ *
    ((∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * ((n - 1).choose j : ℝ) *
      quadraticMonomialPrimitive (n - 2) (1 - 2 * ((k : ℝ) + s - j)) ((k : ℝ) + s - j)) -
     (∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * ((n - 1).choose j : ℝ) *
      quadraticMonomialPrimitive (n - 2) (1 - 2 * ((k : ℝ) + s - j)) ((k : ℝ) + s - j - 1)))

theorem coordinateSquareKernel_eq_piece (n k : ℕ) (hn : 3 ≤ n) (hk : k < n)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    coordinateSquareKernel n ((k : ℝ) + s) = coordinateSquareKernelPiece n k s := by
  rw [coordinateSquareKernel_eq_formula n hn]
  unfold coordinateSquareKernelFormula coordinateSquareKernelPiece
  have hfirst : (∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * ((n - 1).choose j : ℝ) *
      quadraticPowerPrimitive (n - 2) (1 - 2 * ((k : ℝ) + s - j)) ((k : ℝ) + s - j)) =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * ((n - 1).choose j : ℝ) *
        quadraticMonomialPrimitive (n - 2) (1 - 2 * ((k : ℝ) + s - j)) ((k : ℝ) + s - j) := by
    calc
      _ = ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * ((n - 1).choose j : ℝ) *
          quadraticPowerPrimitive (n - 2) (1 - 2 * ((k : ℝ) + s - j)) ((k : ℝ) + s - j) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j _ hj
        have hjk : k + 1 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
        have hjR : (k : ℝ) + 1 ≤ j := by exact_mod_cast hjk
        rw [quadraticPowerPrimitive_of_nonpos _ _ _ (by linarith), mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
        have hjR : (j : ℝ) ≤ k := by exact_mod_cast hjk
        rw [quadraticPowerPrimitive_of_nonneg _ _ _ (by linarith)]
  have hsecond : (∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * ((n - 1).choose j : ℝ) *
      quadraticPowerPrimitive (n - 2) (1 - 2 * ((k : ℝ) + s - j)) ((k : ℝ) + s - j - 1)) =
      ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * ((n - 1).choose j : ℝ) *
        quadraticMonomialPrimitive (n - 2) (1 - 2 * ((k : ℝ) + s - j)) ((k : ℝ) + s - j - 1) := by
    calc
      _ = ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * ((n - 1).choose j : ℝ) *
          quadraticPowerPrimitive (n - 2) (1 - 2 * ((k : ℝ) + s - j)) ((k : ℝ) + s - j - 1) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j _ hj
        have hjk : k ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
        have hjR : (k : ℝ) ≤ j := by exact_mod_cast hjk
        rw [quadraticPowerPrimitive_of_nonpos _ _ _ (by linarith), mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j + 1 ≤ k := by simpa only [Finset.mem_range, Nat.add_one_le_iff] using hj
        have hjR : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
        rw [quadraticPowerPrimitive_of_nonneg _ _ _ (by linarith)]
  simpa only [mul_sub, Finset.sum_sub_distrib] using
    congrArg (fun x : ℝ => (Nat.factorial (n - 2) : ℝ)⁻¹ * x)
      (congrArg₂ (fun x y : ℝ => x - y) hfirst hsecond)

def varianceKernelGap (n : ℕ) (t : ℝ) : ℝ :=
  4 * t ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) * unitSumSplineDensity n t - varianceKernel n t

theorem varianceKernelGap_eq_piece (n k : ℕ) (hn : 3 ≤ n) (hk : k < n)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    varianceKernelGap n ((k : ℝ) + s) =
      4 * ((k : ℝ) + s) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) *
        ((Nat.factorial (n - 1) : ℝ)⁻¹ * Certificate.splinePiece n k s) -
      ((n : ℝ) * coordinateSquareKernelPiece n k s -
        ((n : ℝ) - 2 * ((k : ℝ) + s)) ^ 2 / n *
          ((Nat.factorial (n - 1) : ℝ)⁻¹ * Certificate.splinePiece n k s)) / ((n : ℝ) - 1) := by
  unfold varianceKernelGap varianceKernel
  rw [coordinateSquareKernel_eq_piece n k hn hk s hs0 hs1]
  unfold unitSumSplineDensity
  rw [unnormalizedSpline_eq_piece n k (by omega) (by omega) s hs0 hs1]

theorem varianceKernelGap_five_zero (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    varianceKernelGap 5 s = 0 := by
  have h := varianceKernelGap_eq_piece 5 0 (by decide) (by decide) s hs0 hs1
  norm_num [coordinateSquareKernelPiece, quadraticMonomialPrimitive, Certificate.splinePiece,
    Finset.sum_range_succ, Nat.choose_two_right] at h
  rw [h]
  ring

theorem varianceKernelGap_five_one (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    varianceKernelGap 5 (1 + s) = s ^ 4 * (5 - 2 * s) / 36 := by
  have h := varianceKernelGap_eq_piece 5 1 (by decide) (by decide) s hs0 hs1
  norm_num [coordinateSquareKernelPiece, quadraticMonomialPrimitive, Certificate.splinePiece,
    Finset.sum_range_succ, Nat.choose_two_right] at h
  rw [h]
  ring

theorem varianceKernelGap_five_two (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    varianceKernelGap 5 (2 + s) =
      (6 * s ^ 5 + (25 / 4 : ℝ) * s ^ 2 + 10 * s + 3 + 15 * s ^ 2 * (1 / 4 - s ^ 2)) / 36 := by
  have h := varianceKernelGap_eq_piece 5 2 (by decide) (by decide) s hs0 hs1
  norm_num [coordinateSquareKernelPiece, quadraticMonomialPrimitive, Certificate.splinePiece,
    Finset.sum_range_succ, Nat.choose_two_right] at h
  rw [h]
  ring

theorem varianceKernelGap_six_zero (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    varianceKernelGap 6 s = 0 := by
  have h := varianceKernelGap_eq_piece 6 0 (by decide) (by decide) s hs0 hs1
  norm_num [coordinateSquareKernelPiece, quadraticMonomialPrimitive, Certificate.splinePiece,
    Finset.sum_range_succ, Nat.choose_two_right] at h
  rw [h]
  ring

theorem varianceKernelGap_six_one (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    varianceKernelGap 6 (1 + s) = s ^ 5 * (3 - s) / 105 := by
  have h := varianceKernelGap_eq_piece 6 1 (by decide) (by decide) s hs0 hs1
  norm_num [coordinateSquareKernelPiece, quadraticMonomialPrimitive, Certificate.splinePiece,
    Finset.sum_range_succ, Nat.choose_two_right] at h
  rw [h]
  ring

theorem varianceKernelGap_six_two (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    varianceKernelGap 6 (2 + s) =
      (4 * s ^ 6 + 10 * s ^ 3 + 3 * s ^ 2 + 9 * s + 2 +
        12 * s ^ 2 * (1 - s) * (1 + s + s ^ 2)) / 105 := by
  have h := varianceKernelGap_eq_piece 6 2 (by decide) (by decide) s hs0 hs1
  norm_num [coordinateSquareKernelPiece, quadraticMonomialPrimitive, Certificate.splinePiece,
    Finset.sum_range_succ, Nat.choose_two_right] at h
  rw [h]
  ring

theorem varianceKernel_five_upper (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 5 / 2) :
    varianceKernel 5 t ≤ 4 * t ^ 2 / (5 * 6) * unitSumSplineDensity 5 t := by
  have hgap : 0 ≤ varianceKernelGap 5 t := by
    by_cases h1 : t ≤ 1
    · rw [varianceKernelGap_five_zero t ht0 h1]
    · by_cases h2 : t ≤ 2
      · have h := varianceKernelGap_five_one (t - 1) (by linarith) (by linarith)
        rw [show 1 + (t - 1) = t by ring] at h
        rw [h]
        have hp : 0 ≤ 5 - 2 * (t - 1) := by linarith
        positivity
      · have h := varianceKernelGap_five_two (t - 2) (by linarith) (by linarith)
        rw [show 2 + (t - 2) = t by ring] at h
        rw [h]
        have hs : 0 ≤ t - 2 := by linarith
        have hq : 0 ≤ 1 / 4 - (t - 2) ^ 2 := by nlinarith
        positivity
  unfold varianceKernelGap at hgap
  norm_num at hgap ⊢
  linarith

theorem varianceKernel_six_upper (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 3) :
    varianceKernel 6 t ≤ 4 * t ^ 2 / (6 * 7) * unitSumSplineDensity 6 t := by
  have hgap : 0 ≤ varianceKernelGap 6 t := by
    by_cases h1 : t ≤ 1
    · rw [varianceKernelGap_six_zero t ht0 h1]
    · by_cases h2 : t ≤ 2
      · have h := varianceKernelGap_six_one (t - 1) (by linarith) (by linarith)
        rw [show 1 + (t - 1) = t by ring] at h
        rw [h]
        have hs : 0 ≤ t - 1 := by linarith
        have hp : 0 ≤ 3 - (t - 1) := by linarith
        positivity
      · have h := varianceKernelGap_six_two (t - 2) (by linarith) (by linarith)
        rw [show 2 + (t - 2) = t by ring] at h
        rw [h]
        have hs : 0 ≤ t - 2 := by linarith
        have hq : 0 ≤ 1 - (t - 2) := by linarith
        positivity
  unfold varianceKernelGap at hgap
  norm_num at hgap ⊢
  linarith

end
end ENT.Small
