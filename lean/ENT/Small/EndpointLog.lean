module

public import ENT.Spline.PositiveInterior
public import ENT.Certificate.PolynomialSemantics
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Lebesgue integrability of the diagonal log density on its entire support,
including the support endpoints. Polynomial cells give a finite cover; the
general meromorphic log theorem controls their zeros without discarding an
unproved endpoint term. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Polynomial
open scoped BigOperators

namespace ENT.Small

noncomputable section

def unitCellPolynomial (n k : ℕ) : Polynomial ℝ :=
  C ((Nat.factorial (n - 1) : ℝ)⁻¹) *
    (Certificate.splinePolynomial n k).comp (X - C (k : ℝ))

theorem unitCellPolynomial_eval (n k : ℕ) (x : ℝ) :
    (unitCellPolynomial n k).eval x = (Nat.factorial (n - 1) : ℝ)⁻¹ *
      Certificate.splinePiece n k (x - (k : ℝ)) := by
  simp only [unitCellPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
    Certificate.splinePolynomial_eval]

theorem unitSumSplineDensity_eq_unitCellPolynomial (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n)
    (x : ℝ) (hx : x ∈ Icc (k : ℝ) ((k : ℝ) + 1)) :
    Spline.unitSumSplineDensity n x = (unitCellPolynomial n k).eval x := by
  rw [unitCellPolynomial_eval, Spline.unitSumSplineDensity]
  congr 1
  have h := Spline.unnormalizedSpline_eq_piece n k hn hk (x - (k : ℝ))
    (by linarith [hx.1]) (by linarith [hx.2])
  simpa only [add_sub_cancel] using h

theorem intervalIntegrable_log_unitSumSplineDensity_cell (n k : ℕ)
    (hn : 2 ≤ n) (hk : k ≤ n) :
    IntervalIntegrable (fun x => Real.log (Spline.unitSumSplineDensity n x)) volume
      (k : ℝ) ((k : ℝ) + 1) := by
  have ha := (AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) (unitCellPolynomial n k)).mono
    (Set.subset_univ (Set.uIcc (k : ℝ) ((k : ℝ) + 1)))
  have hi := ha.meromorphicOn.intervalIntegrable_log
  apply hi.congr_uIoo
  intro x hx
  have hx' : x ∈ Ioo (k : ℝ) ((k : ℝ) + 1) := by
    simpa only [Set.uIoo_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] using hx
  change Real.log ((unitCellPolynomial n k).eval x) = Real.log (Spline.unitSumSplineDensity n x)
  rw [unitSumSplineDensity_eq_unitCellPolynomial n k hn hk x ⟨hx'.1.le, hx'.2.le⟩]

theorem intervalIntegrable_log_unitSumSplineDensity (n : ℕ) (hn : 2 ≤ n) :
    IntervalIntegrable (fun x => Real.log (Spline.unitSumSplineDensity n x)) volume 0 (n : ℝ) := by
  have h := IntervalIntegrable.trans_iterate (a := fun k : ℕ => (k : ℝ)) (n := n)
    (fun k hk => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        intervalIntegrable_log_unitSumSplineDensity_cell n k hn hk.le)
  simpa only [Nat.cast_zero] using h

theorem intervalIntegrable_log_diagonalSplineDensity (n : ℕ) (hn : 2 ≤ n) :
    IntervalIntegrable (fun x => Real.log (Spline.diagonalSplineDensity n x)) volume
      (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hs := Real.sqrt_pos.mpr hnR
  have hu := intervalIntegrable_log_unitSumSplineDensity n hn
  have hcomp : IntervalIntegrable (fun x => Real.log (Spline.unitSumSplineDensity n
      (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2))) volume
      (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := by
    have h := (((hu.comp_mul_left (c := (1 / 2 : ℝ))).comp_sub_left (n : ℝ)).comp_mul_left
      (c := Real.sqrt (n : ℝ))).symm
    convert h using 1
    · funext x
      congr 2
      ring
    · field_simp
      rw [Real.sq_sqrt hnR.le]
      ring
    · field_simp
      rw [Real.sq_sqrt hnR.le]
      ring
  have hadd : IntervalIntegrable (fun x => Real.log (Real.sqrt (n : ℝ) / 2) +
      Real.log (Spline.unitSumSplineDensity n (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2))) volume
      (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := intervalIntegrable_const.add hcomp
  apply hadd.congr_uIoo
  intro x hx
  have hx' : x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := by
    simpa only [Set.uIoo_of_le (by linarith : -Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ))] using hx
  have hq := Spline.diagonalSplineDensity_pos n hn x hx'
  have hD : Spline.unitSumSplineDensity n (((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2) ≠ 0 := by
    intro hz
    unfold Spline.diagonalSplineDensity at hq
    rw [hz, mul_zero] at hq
    exact (lt_irrefl 0) hq
  exact (Real.log_mul (div_ne_zero hs.ne' (by norm_num)) hD).symm

theorem integrableOn_log_diagonalSplineDensity_support (n : ℕ) (hn : 2 ≤ n) :
    IntegrableOn (fun x => Real.log (Spline.diagonalSplineDensity n x))
      (Icc (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) volume := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le
    (show -Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) by linarith [Real.sqrt_nonneg (n : ℝ)])).mp
  exact intervalIntegrable_log_diagonalSplineDensity n hn

theorem integrable_mul_log_diagonalSplineDensity_support (n : ℕ) (hn : 2 ≤ n)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {M : ℝ}
    (hM : ∀ x, f x ≤ M)
    (hsupport : ∀ x, x ∉ Icc (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) → f x = 0) :
    Integrable (fun x => f x * Real.log (Spline.diagonalSplineDensity n x)) volume := by
  have hi : IntegrableOn (fun x => f x * Real.log (Spline.diagonalSplineDensity n x))
      (Icc (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) volume :=
    (integrableOn_log_diagonalSplineDensity_support n hn).bdd_mul
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hM x)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [hsupport x hx, zero_mul]

/-- With Lean's real logarithm, the function is zero outside the support.
Support compatibility is still required separately in every KL application. -/
theorem integrable_log_diagonalSplineDensity (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun x => Real.log (Spline.diagonalSplineDensity n x)) volume := by
  apply (integrableOn_log_diagonalSplineDensity_support n hn).integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [Spline.diagonalSplineDensity_eq_zero_of_not_mem n hn x hx, Real.log_zero]

end
end ENT.Small
