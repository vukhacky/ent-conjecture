module

public import ENT.Small.ConditionalKernelCells
public import ENT.Small.ConditionalKernelRegularity
public import ENT.Spline.CellGluing
public import ENT.Spline.SupportInterior
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import ENT.Small.ConditionalKernelLaw
public import ENT.Small.LocalThresholds
public import ENT.Small.LocalDeficit

@[expose] public section
attribute [local instance 1001] NormedField.toNormedSpace

/-! ## HessianKernelPolynomial -/
/-! Polynomial representation and genuine second derivatives of the
conditional-variance kernels in dimensions five and six, including knots. -/

set_option autoImplicit false
open Set Polynomial
open scoped BigOperators ContDiff

namespace ENT.Small
noncomputable section
open Spline

def kernelPolynomialFive : ℕ → Polynomial ℝ
  | 0 => C (1 / 180) * X ^ 6
  | 1 => C (1 / 180) * (C (-4) * X ^ 6 + C 6 * X ^ 5 - C 15 * X ^ 4 +
      C 20 * X ^ 3 + C 15 * X ^ 2 + C 6 * X + C 1)
  | _ => C (1 / 180) * (C 6 * X ^ 6 - C 18 * X ^ 5 + C 45 * X ^ 4 -
      C 60 * X ^ 3 - C 15 * X ^ 2 + C 42 * X + C 29)

def kernelPolynomialSix : ℕ → Polynomial ℝ
  | 0 => C (1 / 1260) * X ^ 7
  | 1 => C (1 / 1260) * (C (-5) * X ^ 7 + C 7 * X ^ 6 - C 21 * X ^ 5 +
      C 35 * X ^ 4 + C 35 * X ^ 3 + C 21 * X ^ 2 + C 7 * X + C 1)
  | _ => C (1 / 630) * (C 5 * X ^ 7 - C 14 * X ^ 6 + C 42 * X ^ 5 -
      C 70 * X ^ 4 - C 35 * X ^ 3 + C 63 * X ^ 2 + C 98 * X + C 40)

theorem unitSumSplineDensity_eq_cell (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    unitSumSplineDensity n ((k : ℝ) + s) =
      (Nat.factorial (n - 1) : ℝ)⁻¹ * Certificate.splinePiece n k s := by
  rw [unitSumSplineDensity, unnormalizedSpline_eq_piece n k hn hk s hs0 hs1]

theorem unitSumSplineDensity_of_nonpos (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : t ≤ 0) :
    unitSumSplineDensity n t = 0 := by
  rcases eq_or_lt_of_le ht with rfl | hlt
  · exact unitSumSplineDensity_zero n hn
  · apply unitSumSplineDensity_eq_zero_of_not_mem n hn t
    intro h
    linarith [h.1]

theorem varianceKernel_eq_piece_data (n k : ℕ) (hn : 3 ≤ n) (hk : k < n)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    varianceKernel n ((k : ℝ) + s) =
      ((n : ℝ) * coordinateSquareKernelPiece n k s -
        ((n : ℝ) - 2 * ((k : ℝ) + s)) ^ 2 / n *
          ((Nat.factorial (n - 1) : ℝ)⁻¹ * Certificate.splinePiece n k s)) / ((n : ℝ) - 1) := by
  unfold varianceKernel
  rw [coordinateSquareKernel_eq_piece n k hn hk s hs0 hs1,
    unitSumSplineDensity_eq_cell n k (by omega) (by omega) s hs0 hs1]

theorem varianceKernel_five_eq_polynomial (k : ℕ) (hk : k ≤ 2)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    varianceKernel 5 ((k : ℝ) + s) = (kernelPolynomialFive k).eval s := by
  have h := varianceKernel_eq_piece_data 5 k (by decide) (by omega) s hs0 hs1
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  all_goals
    norm_num [coordinateSquareKernelPiece, quadraticMonomialPrimitive, Certificate.splinePiece,
      Finset.sum_range_succ, Nat.choose_two_right, kernelPolynomialFive] at h ⊢
    rw [h]
    ring

theorem varianceKernel_six_eq_polynomial (k : ℕ) (hk : k ≤ 2)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    varianceKernel 6 ((k : ℝ) + s) = (kernelPolynomialSix k).eval s := by
  have h := varianceKernel_eq_piece_data 6 k (by decide) (by omega) s hs0 hs1
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  all_goals
    norm_num [coordinateSquareKernelPiece, quadraticMonomialPrimitive, Certificate.splinePiece,
      Finset.sum_range_succ, Nat.choose_two_right, kernelPolynomialSix] at h ⊢
    rw [h]
    ring

theorem varianceKernel_second_of_polynomial {n k : ℕ} (hn : 4 ≤ n)
    (P : Polynomial ℝ)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, varianceKernel n ((k : ℝ) + s) = P.eval s)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    deriv (deriv (varianceKernel n)) ((k : ℝ) + s) = P.derivative.derivative.eval s := by
  let g : ℝ → ℝ := fun x => P.eval (x - (k : ℝ))
  have hcont : ContDiff ℝ 2 (fun x : ℝ => P.eval x) := by
    clear hP g
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.add hQ
    | monomial m a =>
      simpa only [Polynomial.eval_monomial] using
        (contDiff_const.mul (contDiff_id.pow m) : ContDiff ℝ 2 (fun x : ℝ => a*x^m))
  have hg : ContDiff ℝ 2 g := hcont.comp (contDiff_id.sub contDiff_const)
  have heq : EqOn (varianceKernel n) g (Icc (k : ℝ) ((k : ℝ) + 1)) := by
    intro x hx
    have h := hP (x - k) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa only [add_sub_cancel] using h
  have h := iteratedDeriv_eq_of_eqOn_Icc 2 (varianceKernel n) g (k : ℝ) ((k : ℝ) + 1)
    ((k : ℝ) + s) (by linarith) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    (contDiff_varianceKernel 2 n (by omega) (by omega)).contDiffAt hg.contDiffAt heq
  have hd1 : deriv g = fun x => P.derivative.eval (x - (k : ℝ)) := by
    funext x
    have hx := (P.hasDerivAt (x - (k : ℝ))).comp x ((hasDerivAt_id x).sub_const (k : ℝ))
    exact (by simpa only [g, Function.comp_def, id_eq, mul_one] using hx : HasDerivAt g _ x).deriv
  have hd2 : deriv (fun x => P.derivative.eval (x - (k : ℝ))) =
      fun x => P.derivative.derivative.eval (x - (k : ℝ)) := by
    funext x
    have hx := (P.derivative.hasDerivAt (x - (k : ℝ))).comp x ((hasDerivAt_id x).sub_const (k : ℝ))
    have hx' : HasDerivAt (fun y => P.derivative.eval (y - (k : ℝ)))
        (P.derivative.derivative.eval (x - (k : ℝ))) x := by
      simpa only [Function.comp_def, id_eq, mul_one] using hx
    exact hx'.deriv
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, hd1, hd2, add_sub_cancel_left] using h

end
end ENT.Small

/-! ## HessianKernelEquation -/
/-! The exact second-derivative kernel equation required by the Hessian
identity, proved pointwise on the closed support, including every knot. -/

set_option autoImplicit false
open Set Polynomial

namespace ENT.Small
noncomputable section
open Spline

theorem lower_density_eq_previous_piece (n k : ℕ) (hn : 4 ≤ n) (hk : k < n)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    unitSumSplineDensity (n - 2) ((k : ℝ) + s - 1) =
      if k = 0 then 0 else (Nat.factorial (n - 3) : ℝ)⁻¹ * Certificate.splinePiece (n - 2) (k - 1) s := by
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.cast_zero, zero_add, ite_true]
    exact unitSumSplineDensity_of_nonpos (n - 2) (by omega) (s - 1) (by linarith)
  · rw [if_neg hk0]
    have harg : (k : ℝ) + s - 1 = ((k - 1 : ℕ) : ℝ) + s := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      ring
    rw [harg, unitSumSplineDensity_eq_cell (n - 2) (k - 1) (by omega) (by omega) s hs0 hs1]
    congr 2 <;> omega

theorem kernelPolynomialFive_second (k : ℕ) (hk : k ≤ 2)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (kernelPolynomialFive k).derivative.derivative.eval s =
      4 * (unitSumSplineDensity 5 ((k : ℝ) + s) -
        unitSumSplineDensity 3 ((k : ℝ) + s - 1)) := by
  rw [unitSumSplineDensity_eq_cell 5 k (by decide) (by omega) s hs0 hs1,
    show unitSumSplineDensity 3 ((k : ℝ) + s - 1) =
      if k = 0 then 0 else (Nat.factorial (5 - 3) : ℝ)⁻¹ * Certificate.splinePiece (5 - 2) (k - 1) s from
        lower_density_eq_previous_piece 5 k (by decide) (by omega) s hs0 hs1]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  all_goals
    norm_num [kernelPolynomialFive, Polynomial.derivative_mul, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_X_pow, Certificate.splinePiece,
      Finset.sum_range_succ, Nat.choose_two_right]
    ring

theorem kernelPolynomialSix_second (k : ℕ) (hk : k ≤ 2)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (kernelPolynomialSix k).derivative.derivative.eval s =
      4 * (unitSumSplineDensity 6 ((k : ℝ) + s) -
        unitSumSplineDensity 4 ((k : ℝ) + s - 1)) := by
  rw [unitSumSplineDensity_eq_cell 6 k (by decide) (by omega) s hs0 hs1,
    show unitSumSplineDensity 4 ((k : ℝ) + s - 1) =
      if k = 0 then 0 else (Nat.factorial (6 - 3) : ℝ)⁻¹ * Certificate.splinePiece (6 - 2) (k - 1) s from
        lower_density_eq_previous_piece 6 k (by decide) (by omega) s hs0 hs1]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  all_goals
    norm_num [kernelPolynomialSix, Polynomial.derivative_mul, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_X_pow, Certificate.splinePiece,
      Finset.sum_range_succ, Nat.choose_two_right]
    ring

theorem varianceKernel_five_second_cell (k : ℕ) (hk : k ≤ 2)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    deriv (deriv (varianceKernel 5)) ((k : ℝ) + s) =
      4 * (unitSumSplineDensity 5 ((k : ℝ) + s) - unitSumSplineDensity 3 ((k : ℝ) + s - 1)) := by
  rw [varianceKernel_second_of_polynomial (by decide : 4 ≤ 5) (kernelPolynomialFive k)
    (fun x hx => varianceKernel_five_eq_polynomial k hk x hx.1 hx.2) s hs,
    kernelPolynomialFive_second k hk s hs.1 hs.2]

theorem varianceKernel_six_second_cell (k : ℕ) (hk : k ≤ 2)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    deriv (deriv (varianceKernel 6)) ((k : ℝ) + s) =
      4 * (unitSumSplineDensity 6 ((k : ℝ) + s) - unitSumSplineDensity 4 ((k : ℝ) + s - 1)) := by
  rw [varianceKernel_second_of_polynomial (by decide : 4 ≤ 6) (kernelPolynomialSix k)
    (fun x hx => varianceKernel_six_eq_polynomial k hk x hx.1 hx.2) s hs,
    kernelPolynomialSix_second k hk s hs.1 hs.2]

theorem varianceKernel_five_second_half (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 5 / 2) :
    deriv (deriv (varianceKernel 5)) t =
      4 * (unitSumSplineDensity 5 t - unitSumSplineDensity 3 (t - 1)) := by
  by_cases h1 : t ≤ 1
  · simpa only [Nat.cast_zero, zero_add] using
      varianceKernel_five_second_cell 0 (by decide) t ⟨ht0, h1⟩
  · by_cases h2 : t ≤ 2
    · have h := varianceKernel_five_second_cell 1 (by decide) (t - 1) ⟨by linarith, by linarith⟩
      convert h using 1 <;> norm_num <;> congr 2 <;> ring
    · have h := varianceKernel_five_second_cell 2 (by decide) (t - 2) ⟨by linarith, by linarith⟩
      convert h using 1 <;> norm_num <;> congr 2 <;> ring

theorem varianceKernel_six_second_half (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 3) :
    deriv (deriv (varianceKernel 6)) t =
      4 * (unitSumSplineDensity 6 t - unitSumSplineDensity 4 (t - 1)) := by
  by_cases h1 : t ≤ 1
  · simpa only [Nat.cast_zero, zero_add] using
      varianceKernel_six_second_cell 0 (by decide) t ⟨ht0, h1⟩
  · by_cases h2 : t ≤ 2
    · have h := varianceKernel_six_second_cell 1 (by decide) (t - 1) ⟨by linarith, by linarith⟩
      convert h using 1 <;> norm_num <;> congr 2 <;> ring
    · have h := varianceKernel_six_second_cell 2 (by decide) (t - 2) ⟨by linarith, by linarith⟩
      convert h using 1 <;> norm_num <;> congr 2 <;> ring

theorem second_deriv_reflection (f : ℝ → ℝ) (c : ℝ) (hf : ContDiff ℝ 2 f)
    (hsym : ∀ x, f (c - x) = f x) (t : ℝ) :
    deriv (deriv f) (c - t) = deriv (deriv f) t := by
  let g : ℝ → ℝ := fun x => f (c - x)
  have hfun : g = f := funext hsym
  have hd : deriv g = fun x => -deriv f (c - x) := by
    funext x
    have h := ((hf.differentiable (by norm_num) (c - x)).hasDerivAt).comp x
      ((hasDerivAt_const x c).sub (hasDerivAt_id x))
    exact (by simpa only [g, Function.comp_def, id_eq, sub_self, zero_sub, mul_neg_one] using h : HasDerivAt g _ x).deriv
  have h2 : HasDerivAt (fun x => -deriv f (c - x)) (deriv (deriv f) (c - t)) t := by
    have h := ((hf.differentiable_deriv_two (c - t)).hasDerivAt.comp t
      ((hasDerivAt_const t c).sub (hasDerivAt_id t))).neg
    convert h using 1 <;> first | rfl | ring
  calc
    _ = deriv (fun x => -deriv f (c - x)) t := h2.deriv.symm
    _ = deriv (deriv g) t := by rw [hd]
    _ = _ := by rw [hfun]

theorem varianceKernel_second_reflection (n : ℕ) (hn : 4 ≤ n) (t : ℝ) :
    deriv (deriv (varianceKernel n)) ((n : ℝ) - t) = deriv (deriv (varianceKernel n)) t :=
  second_deriv_reflection _ _ (contDiff_varianceKernel 2 n (by omega) (by omega))
    (varianceKernel_reflection n (by omega)) t

theorem shifted_lower_density_reflection (n : ℕ) (hn : 4 ≤ n) (t : ℝ) :
    unitSumSplineDensity (n - 2) ((n : ℝ) - t - 1) = unitSumSplineDensity (n - 2) (t - 1) := by
  have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
  rw [show (n : ℝ) - t - 1 = ((n - 2 : ℕ) : ℝ) - (t - 1) by rw [hn2]; ring,
    unitSumSplineDensity_reflection (n - 2) (by omega)]

theorem varianceKernel_five_second (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 5) :
    deriv (deriv (varianceKernel 5)) t =
      4 * (unitSumSplineDensity 5 t - unitSumSplineDensity 3 (t - 1)) := by
  by_cases hm : t ≤ 5 / 2
  · exact varianceKernel_five_second_half t ht.1 hm
  · have h := varianceKernel_five_second_half (5 - t) (by linarith [ht.2]) (by linarith)
    have hr := varianceKernel_second_reflection 5 (by decide) t
    have hf := unitSumSplineDensity_reflection 5 (by decide) t
    have hl := shifted_lower_density_reflection 5 (by decide) t
    norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hr hf hl
    rw [hr, hf, hl] at h
    exact h

theorem varianceKernel_six_second (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 6) :
    deriv (deriv (varianceKernel 6)) t =
      4 * (unitSumSplineDensity 6 t - unitSumSplineDensity 4 (t - 1)) := by
  by_cases hm : t ≤ 3
  · exact varianceKernel_six_second_half t ht.1 hm
  · have h := varianceKernel_six_second_half (6 - t) (by linarith [ht.2]) (by linarith)
    have hr := varianceKernel_second_reflection 6 (by decide) t
    have hf := unitSumSplineDensity_reflection 6 (by decide) t
    have hl := shifted_lower_density_reflection 6 (by decide) t
    norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hr hf hl
    rw [hr, hf, hl] at h
    exact h

end
end ENT.Small

/-! ## WeightedVariance -/
/-! Exact weighted variance identity for genuine uniform cube variables.
All changes of variables and linearity steps carry integrability proofs. -/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace ENT.Small
noncomputable section
open Spline

theorem diagonal_integral_eq_sum_coordinate (n : ℕ) (hn : 2 ≤ n)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f (projection (diagonal n) x) ∂cubeLaw n) =
      ∫ t, unitSumSplineDensity n t * f (sumToDiagonal n t) := by
  have hlaw : projectionLaw (diagonal n) =
      (volume.withDensity (fun t => ENNReal.ofReal (unitSumSplineDensity n t))).map
        (sumToDiagonal n) := by
    rw [projectionLaw_diagonal_eq_map_sumLaw01, sumLaw01_eq_splineDensity n hn]
    rfl
  have h := congrArg (fun μ : Measure ℝ => ∫ t, f t ∂μ) hlaw
  rw [projectionLaw, integral_map (measurable_projection _).aemeasurable hf.aestronglyMeasurable,
    integral_map (measurable_sumToDiagonal _).aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_unitSumSplineDensity n).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  simpa only [ENNReal.toReal_ofReal (unitSumSplineDensity_nonneg n hn _), smul_eq_mul] using h

theorem integrable_diagonal_iff_sum_coordinate (n : ℕ) (hn : 2 ≤ n)
    (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable (fun x => f (projection (diagonal n) x)) (cubeLaw n) ↔
      Integrable (fun t => unitSumSplineDensity n t * f (sumToDiagonal n t)) volume := by
  have hmap := integrable_map_measure (μ := cubeLaw n) hf.aestronglyMeasurable
    (measurable_projection (diagonal n)).aemeasurable
  have hlaw : projectionLaw (diagonal n) =
      (volume.withDensity (fun t => ENNReal.ofReal (unitSumSplineDensity n t))).map
        (sumToDiagonal n) := by
    rw [projectionLaw_diagonal_eq_map_sumLaw01, sumLaw01_eq_splineDensity n hn]
    rfl
  change Integrable f (projectionLaw (diagonal n)) ↔ _ at hmap
  rw [hlaw] at hmap
  have hmap2 := integrable_map_measure
    (μ := volume.withDensity (fun t => ENNReal.ofReal (unitSumSplineDensity n t))) hf.aestronglyMeasurable
    (measurable_sumToDiagonal n).aemeasurable
  have hwd := integrable_withDensity_iff_integrable_smul'
    (μ := volume) (g := fun t => f (sumToDiagonal n t))
    (continuous_unitSumSplineDensity n).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
  simpa only [Function.comp_def,
    ENNReal.toReal_ofReal (unitSumSplineDensity_nonneg n hn _), smul_eq_mul] using
    hmap.symm.trans (hmap2.trans hwd)

theorem integrable_projection_sq_diagonal_test {n : ℕ} (b : Fin n → ℝ) {f : ℝ → ℝ}
    (hf : Integrable (fun x => f (projection (diagonal n) x)) (cubeLaw n)) :
    Integrable (fun x => projection b x^2 * f (projection (diagonal n) x)) (cubeLaw n) := by
  have hfun : (fun x : Fin n → ℝ => projection b x^2 * f (projection (diagonal n) x)) =
      (fun x => ∑ i, ∑ j, b i*b j*((x i*x j)*f (projection (diagonal n) x))) := by
    funext x
    simp only [projection, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_coordinate_pair_diagonal_test i j hf).const_mul _

theorem integrable_coordinateKernel_test (n : ℕ) (hn : 3 ≤ n)
    (f : ℝ → ℝ) (hm : Measurable f)
    (hf : Integrable (fun t => unitSumSplineDensity n t*f (sumToDiagonal n t)) volume) :
    Integrable (fun t => coordinateSquareKernel n t*f (sumToDiagonal n t)) volume := by
  apply hf.norm.mono'
    (((measurable_coordinateSquareKernel n hn).mul (hm.comp (measurable_sumToDiagonal n))).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun t => by
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (coordinateSquareKernel_nonneg n hn t),
      abs_of_nonneg (unitSumSplineDensity_nonneg n (by omega) t)]
    exact mul_le_mul_of_nonneg_right (coordinateSquareKernel_le_density n hn t) (abs_nonneg _)

theorem integral_zero_sum_projection_sq_eq_varianceKernel {n : ℕ} (hn : 3 ≤ n)
    (b : Fin n → ℝ) (hb : ∑ i,b i = 0) (f : ℝ → ℝ) (hm : Measurable f)
    (hf : Integrable (fun x => f (projection (diagonal n) x)) (cubeLaw n)) :
    (∫ x, projection b x^2*f (projection (diagonal n) x) ∂cubeLaw n) =
      perturbationEnergy b * ∫ t, varianceKernel n t*f (sumToDiagonal n t) := by
  have hfn := (integrable_diagonal_iff_sum_coordinate n (by omega) f hm).mp hf
  have hK := integrable_coordinateKernel_test n hn f hm hfn
  have hm2 : Measurable (fun x : ℝ => x^2*f x) := (measurable_id.pow_const 2).mul hm
  have hf2 := (integrable_diagonal_iff_sum_coordinate n (by omega)
    (fun x : ℝ => x^2*f x) hm2).mp (integrable_projection_sq_diagonal_test (diagonal n) hf)
  have hA : diagonalTestMoment (n := n) f ⟨0, by omega⟩ ⟨0, by omega⟩ =
      ∫ t, coordinateSquareKernel n t*f (sumToDiagonal n t) := by
    cases n with
    | zero => omega
    | succ m => exact diagonalTestMoment_eq_kernel m (by omega) f hm
  have hT := diagonal_integral_eq_sum_coordinate n (by omega) (fun x : ℝ => x^2*f x) hm2
  have heq (t : ℝ) : varianceKernel n t*f (sumToDiagonal n t) =
      ((n:ℝ)*(coordinateSquareKernel n t*f (sumToDiagonal n t))-
        unitSumSplineDensity n t*(sumToDiagonal n t^2*f (sumToDiagonal n t)))/((n:ℝ)-1) := by
    simp only [varianceKernel, sumToDiagonal, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  have hB : (∫ t, varianceKernel n t*f (sumToDiagonal n t)) =
      ((n:ℝ)*(∫ t,coordinateSquareKernel n t*f (sumToDiagonal n t))-
        ∫ t,unitSumSplineDensity n t*(sumToDiagonal n t^2*f (sumToDiagonal n t)))/((n:ℝ)-1) := by
    simp_rw [heq]
    rw [integral_div, integral_sub (hK.const_mul _) hf2, integral_const_mul]
  rw [integral_zero_sum_projection_sq_diagonal_test (by omega) b hb hf, hA, hT, hB]
  ring

end
end ENT.Small

/-! ## FiveSixGeometry -/
/-! The actual fixed-support chart reaches the exterior thresholds in
dimensions five and six. Simple rational coordinate bounds suffice. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators

namespace ENT.Small
noncomputable section

def diagonalAlignment {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  Real.sqrt (n:ℝ)*coefficientMean a

def centeredChart {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  a i/diagonalAlignment a-diagonal n i

theorem diagonalAlignment_sq {n : ℕ} (hn : 0<n) (a : Fin n → ℝ) (ha : IsUnit a) :
    diagonalAlignment a^2 = 1-centeredEnergy a := by
  have h := centeredEnergy_add_mean_sq hn a
  rw [ha] at h
  unfold diagonalAlignment
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  linarith

theorem diagonalAlignment_pos {n : ℕ} (hn : 0<n) (a : Fin n → ℝ) (ha : IsUnit a)
    (ha0 : ∀ i,0≤a i) (hu : centeredEnergy a<1) : 0<diagonalAlignment a := by
  have h0 : 0≤diagonalAlignment a :=
    mul_nonneg (Real.sqrt_nonneg _) (coefficientMean_nonneg a ha0)
  nlinarith [diagonalAlignment_sq hn a ha]

theorem centeredChart_sum {n : ℕ} (hn : 0<n) (a : Fin n → ℝ)
    (hc : 0<diagonalAlignment a) : ∑ i,centeredChart a i=0 := by
  have hs : Real.sqrt (n:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hm : coefficientMean a≠0 := by
    intro h
    have : diagonalAlignment a=0 := by simp [diagonalAlignment,h]
    linarith
  simp only [centeredChart,Finset.sum_sub_distrib,←Finset.sum_div,sum_diagonal hn,
    sum_eq_card_mul_mean hn a,diagonalAlignment]
  field_simp
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]

theorem centeredChart_fixed {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    fixedSupportCoefficients (centeredChart a) i=a i/diagonalAlignment a := by
  unfold fixedSupportCoefficients centeredChart
  ring

theorem centeredChart_energy {n : ℕ} (hn : 0<n) (a : Fin n → ℝ) (ha : IsUnit a)
    (hc : 0<diagonalAlignment a) :
    perturbationEnergy (centeredChart a)=centeredEnergy a/(1-centeredEnergy a) := by
  have h := fixedSupportCoefficients_sum_sq hn (centeredChart a) (centeredChart_sum hn a hc)
  simp_rw [centeredChart_fixed,div_pow] at h
  rw [←Finset.sum_div,ha] at h
  have hs := diagonalAlignment_sq hn a ha
  have hc2 : diagonalAlignment a^2≠0 := pow_ne_zero _ hc.ne'
  have he : perturbationEnergy (centeredChart a)=(1-diagonalAlignment a^2)/diagonalAlignment a^2 := by
    apply (eq_div_iff hc2).mpr
    have hh := (div_eq_iff hc2).mp h
    nlinarith only [hh]
  rw [he,hs]
  ring

theorem normalized_centeredChart {n : ℕ} (hn : 0<n) (a : Fin n → ℝ) (ha : IsUnit a)
    (hc : 0<diagonalAlignment a) : normalizedPerturbation (centeredChart a)=a := by
  have h := fixedSupportCoefficients_sum_sq hn (centeredChart a) (centeredChart_sum hn a hc)
  simp_rw [centeredChart_fixed,div_pow] at h
  rw [←Finset.sum_div,ha] at h
  have hs : Real.sqrt (1+perturbationEnergy (centeredChart a))=(diagonalAlignment a)⁻¹ := by
    rw [←h,one_div,←inv_pow,Real.sqrt_sq (inv_nonneg.mpr hc.le)]
  funext i
  rw [normalizedPerturbation,centeredChart_fixed,hs]
  field_simp

theorem centeredEnergy_le_deficit_of_coordinate_sum_lower {n : ℕ} (hn : 0<n)
    (a : Fin n → ℝ) {c : ℝ} (hc : 0<c)
    (ha : ∀ i,c≤a i+diagonal n i) : centeredEnergy a≤deficit a/c^2 := by
  have hsum : c^2*(∑ i,(a i-(Real.sqrt (n:ℝ))⁻¹)^2)≤deficit a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hs : c^2≤(a i+diagonal n i)^2 :=
      pow_le_pow_left₀ hc.le (ha i) 2
    have h := mul_le_mul_of_nonneg_right hs (sq_nonneg (a i-diagonal n i))
    change c^2*(a i-diagonal n i)^2≤(a i^2-(n:ℝ)⁻¹)^2
    calc
      _ ≤ (a i+diagonal n i)^2*(a i-diagonal n i)^2 := h
      _ = (a i^2-(diagonal n i)^2)^2 := by ring
      _ = _ := by rw [diagonal_sq]
  have hce := centeredEnergy_le_sum_sq_shift hn a ((Real.sqrt (n:ℝ))⁻¹)
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hce (sq_nonneg c)]

theorem five_small_deficit_coordinate_sum (a : Fin 5 → ℝ) (ha0 : ∀ i,0≤a i)
    (hδ : deficit a≤7/12500) (i : Fin 5) : (17:ℝ)/20≤a i+diagonal 5 i := by
  have hi : (a i^2-(5:ℝ)⁻¹)^2≤deficit a :=
    Finset.single_le_sum (fun j _=>sq_nonneg (a j^2-(5:ℝ)⁻¹)) (Finset.mem_univ i)
  have hai : (41:ℝ)/100<a i := by
    have hs : (17:ℝ)/100<a i^2 := by norm_num at hi; nlinarith
    nlinarith [ha0 i]
  have hr2 := diagonal_sq 5 i
  have hr0 : 0≤diagonal 5 i := by unfold diagonal; positivity
  have hr : (11:ℝ)/25<diagonal 5 i := by norm_num at hr2; nlinarith
  linarith

theorem six_small_deficit_coordinate_sum (a : Fin 6 → ℝ) (ha0 : ∀ i,0≤a i)
    (hδ : deficit a≤1/6000) (i : Fin 6) : (4:ℝ)/5≤a i+diagonal 6 i := by
  have hi : (a i^2-(6:ℝ)⁻¹)^2≤deficit a :=
    Finset.single_le_sum (fun j _=>sq_nonneg (a j^2-(6:ℝ)⁻¹)) (Finset.mem_univ i)
  have hai : (49:ℝ)/125<a i := by
    have hs : (1537:ℝ)/10000<a i^2 := by norm_num at hi; nlinarith
    nlinarith [ha0 i]
  have hr2 := diagonal_sq 6 i
  have hr0 : 0≤diagonal 6 i := by unfold diagonal; positivity
  have hr : (51:ℝ)/125<diagonal 6 i := by norm_num at hr2; nlinarith
  linarith

theorem five_centeredChart_local (a : Fin 5 → ℝ) (ha : IsUnit a) (ha0 : ∀ i,0≤a i)
    (hδ : deficit a≤7/12500) :
    (∑ i,centeredChart a i=0) ∧ normalizedPerturbation (centeredChart a)=a ∧
      perturbationEnergy (centeredChart a)≤(29/1000:ℝ)^2 := by
  have hu := centeredEnergy_le_deficit_of_coordinate_sum_lower (by decide : 0<5)
    a (by norm_num : (0:ℝ)<17/20) (five_small_deficit_coordinate_sum a ha0 hδ)
  have hu1 : centeredEnergy a<1 := by norm_num at hu; linarith
  have hc := diagonalAlignment_pos (by decide) a ha ha0 hu1
  refine ⟨centeredChart_sum (by decide) a hc,normalized_centeredChart (by decide) a ha hc,?_⟩
  rw [centeredChart_energy (by decide) a ha hc]
  apply (div_le_iff₀ (by linarith : 0<1-centeredEnergy a)).mpr
  norm_num at hu ⊢
  linarith

theorem six_centeredChart_local (a : Fin 6 → ℝ) (ha : IsUnit a) (ha0 : ∀ i,0≤a i)
    (hδ : deficit a≤1/6000) :
    (∑ i,centeredChart a i=0) ∧ normalizedPerturbation (centeredChart a)=a ∧
      perturbationEnergy (centeredChart a)≤(7/400:ℝ)^2 := by
  have hu := centeredEnergy_le_deficit_of_coordinate_sum_lower (by decide : 0<6)
    a (by norm_num : (0:ℝ)<4/5) (six_small_deficit_coordinate_sum a ha0 hδ)
  have hu1 : centeredEnergy a<1 := by norm_num at hu; linarith
  have hc := diagonalAlignment_pos (by decide) a ha ha0 hu1
  refine ⟨centeredChart_sum (by decide) a hc,normalized_centeredChart (by decide) a ha hc,?_⟩
  rw [centeredChart_energy (by decide) a ha hc]
  apply (div_le_iff₀ (by linarith : 0<1-centeredEnergy a)).mpr
  norm_num at hu ⊢
  linarith

end
end ENT.Small
