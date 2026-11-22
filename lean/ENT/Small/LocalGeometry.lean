module

public import ENT.Basic.Coefficients
public import ENT.Basic.ProjectionSupport
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp

/-! Exact geometry of the zero-sum, fixed-support perturbation of the diagonal. -/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace ENT.Small

noncomputable section

def perturbationEnergy {n : ℕ} (b : Fin n → ℝ) : ℝ := ∑ i, b i ^ 2

def fixedSupportCoefficients {n : ℕ} (b : Fin n → ℝ) (i : Fin n) : ℝ :=
  diagonal n i + b i

def normalizedPerturbation {n : ℕ} (b : Fin n → ℝ) (i : Fin n) : ℝ :=
  fixedSupportCoefficients b i / Real.sqrt (1 + perturbationEnergy b)

theorem perturbationEnergy_nonneg {n : ℕ} (b : Fin n → ℝ) :
    0 ≤ perturbationEnergy b := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem fixedSupportCoefficients_sum_sq {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) :
    (∑ i, fixedSupportCoefficients b i ^ 2) = 1 + perturbationEnergy b := by
  calc
    _ = (∑ i, (diagonal n i) ^ 2) +
        2 * (Real.sqrt (n : ℝ))⁻¹ * (∑ i, b i) + ∑ i, b i ^ 2 := by
      unfold fixedSupportCoefficients diagonal
      simp_rw [add_sq]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 1 + perturbationEnergy b := by rw [isUnit_diagonal hn, hb]; simp [perturbationEnergy]

theorem normalizedPerturbation_isUnit {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) : IsUnit (normalizedPerturbation b) := by
  have hz : 0 < 1 + perturbationEnergy b := by linarith [perturbationEnergy_nonneg b]
  unfold IsUnit normalizedPerturbation
  simp_rw [div_pow, Real.sq_sqrt hz.le]
  rw [← Finset.sum_div, fixedSupportCoefficients_sum_sq hn b hb, div_self hz.ne']

theorem sum_diagonal {n : ℕ} (hn : 0 < n) :
    (∑ i : Fin n, diagonal n i) = Real.sqrt (n : ℝ) := by
  have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  simp only [diagonal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ = Real.sqrt (n : ℝ) ^ 2 * (Real.sqrt (n : ℝ))⁻¹ := by
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    _ = Real.sqrt (n : ℝ) := by field_simp

theorem fixedSupportCoefficients_sum {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℝ) (hb : ∑ i, b i = 0) :
    (∑ i, fixedSupportCoefficients b i) = Real.sqrt (n : ℝ) := by
  simp only [fixedSupportCoefficients, Finset.sum_add_distrib, sum_diagonal hn, hb, add_zero]

theorem fixedSupportCoefficients_pos {n : ℕ} (hn : 0 < n) (b : Fin n → ℝ)
    {γ : ℝ} (hγ : γ < 1) (hb : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ) (i : Fin n) :
    0 < fixedSupportCoefficients b i := by
  have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hi : |b i| < (Real.sqrt (n : ℝ))⁻¹ := by
    rw [← one_div]
    apply (lt_div_iff₀ hs).mpr
    nlinarith [hb i]
  unfold fixedSupportCoefficients diagonal
  linarith [neg_abs_le (b i)]

theorem zero_sum_coordinate_sq_bound {n : ℕ} (b : Fin n → ℝ)
    (hb : ∑ i, b i = 0) (i : Fin n) :
    (n : ℝ) * (b i) ^ 2 ≤ ((n : ℝ) - 1) * perturbationEnergy b := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨i⟩
  have hsum : (∑ j ∈ Finset.univ.erase i, b j) = -b i := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := b) (Finset.mem_univ i)
    rw [hb] at h
    linarith
  have hsq : (∑ j ∈ Finset.univ.erase i, b j ^ 2) = perturbationEnergy b - b i ^ 2 := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := fun j => b j ^ 2) (Finset.mem_univ i)
    change _ + _ = perturbationEnergy b at h
    linarith
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i)
    b (fun _ : Fin n => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hsum, hsq, neg_sq] at h
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h
  nlinarith

theorem zero_sum_coordinate_abs_bound {n : ℕ} (b : Fin n → ℝ)
    (hb : ∑ i, b i = 0) (i : Fin n) :
    Real.sqrt (n : ℝ) * |b i| ≤
      Real.sqrt ((n : ℝ) - 1) * Real.sqrt (perturbationEnergy b) := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨i⟩
  have hn1 : 0 ≤ (n : ℝ) - 1 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), sq_abs,
    Real.sq_sqrt hn1, Real.sq_sqrt (perturbationEnergy_nonneg b)]
  exact zero_sum_coordinate_sq_bound b hb i

theorem abs_projection_le_zero_sum_gap {n : ℕ} (b x : Fin n → ℝ)
    (hb : ∑ i, b i = 0) (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1)
    {B : ℝ} (hB : ∀ i, |b i| ≤ B) :
    |projection b x| ≤ B * ((n : ℝ) - |∑ i, x i|) := by
  have hminus : |projection b x| ≤ B * ((n : ℝ) - ∑ i, x i) := by
    have heq : projection b x = -(∑ i, b i * (1 - x i)) := by
      simp only [projection, mul_sub, mul_one, Finset.sum_sub_distrib, hb, zero_sub, neg_neg]
    rw [heq, abs_neg]
    calc
      _ ≤ ∑ i, |b i * (1 - x i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |b i| * (1 - x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 - x i by linarith [(hx i).2])]
      _ ≤ ∑ i, B * (1 - x i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hB i) (by linarith [(hx i).2])
      _ = _ := by
        simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hplus : |projection b x| ≤ B * ((n : ℝ) + ∑ i, x i) := by
    have heq : projection b x = ∑ i, b i * (1 + x i) := by
      simp only [projection, mul_add, mul_one, Finset.sum_add_distrib, hb, zero_add]
    rw [heq]
    calc
      _ ≤ ∑ i, |b i * (1 + x i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |b i| * (1 + x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 + x i by linarith [(hx i).1])]
      _ ≤ ∑ i, B * (1 + x i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hB i) (by linarith [(hx i).1])
      _ = _ := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  by_cases hsign : 0 ≤ ∑ i, x i
  · simpa only [abs_of_nonneg hsign] using hminus
  · simpa only [abs_of_neg (lt_of_not_ge hsign), sub_neg_eq_add] using hplus

theorem projection_zero_sum_support_distance {n : ℕ} (hn : 0 < n)
    (b x : Fin n → ℝ) (hb : ∑ i, b i = 0)
    (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1)
    {γ : ℝ} (hγ : ∀ i, Real.sqrt (n : ℝ) * |b i| ≤ γ) :
    |projection b x| ≤ γ * (Real.sqrt (n : ℝ) - |projection (diagonal n) x|) := by
  have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hB : ∀ i, |b i| ≤ γ / Real.sqrt (n : ℝ) := by
    intro i
    apply (le_div_iff₀ hs).mpr
    simpa only [mul_comm] using hγ i
  have h := abs_projection_le_zero_sum_gap b x hb hx hB
  have heq : (γ / Real.sqrt (n : ℝ)) * ((n : ℝ) - |∑ i, x i|) =
      γ * (Real.sqrt (n : ℝ) - |projection (diagonal n) x|) := by
    unfold projection diagonal
    rw [← Finset.mul_sum, abs_mul, abs_of_pos (inv_pos.mpr hs)]
    field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  exact h.trans_eq heq

end
end ENT.Small
