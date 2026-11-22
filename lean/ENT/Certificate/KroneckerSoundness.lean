module

public import ENT.Certificate.KroneckerInjective
public import ENT.Certificate.KroneckerBounds
public import ENT.Certificate.KroneckerEval
public import ENT.Certificate.BlockSoundness

/-! Large-base polynomial identity checks imply the curvature inequality for the represented spline cell. -/

@[expose] public section
set_option autoImplicit false
open Polynomial

namespace ENT.Certificate.Kronecker
noncomputable section

theorem valid_curvature_poly (c : Pure.CellData) (rBase bBase : ℤ)
    (h : Valid c rBase bBase) :
    Block.poly c.rCoeffs = Block.poly (Pure.curvatureCoeffs c.n c.k c.pCoeffs) := by
  apply eq_of_eval_eq_of_coeff_bounds _ _ rBase
    (sumAbs c.rCoeffs)
    (curvatureCoeffBound c.n c.k c.pCoeffs.length (sumAbs c.pCoeffs))
    (list_poly_bound c.rCoeffs).2
    (curvature_coeff_natAbs_le c.n c.k c.pCoeffs)
    h.r_bound
  rw [← intEval_eq, ← intEval_eq, intEval_curvature]
  exact h.r_eval

theorem valid_bernstein_poly (c : Pure.CellData) (rBase bBase : ℤ)
    (h : Valid c rBase bBase) :
    Block.poly c.transformedCoeffs =
      BlockBernstein.bernsteinPolynomial c.degreeBound c.bernsteinNumerators := by
  apply eq_of_eval_eq_of_coeff_bounds _ _ bBase
    (sumAbs c.transformedCoeffs)
    (bernsteinCoeffBound c.degreeBound c.bernsteinNumerators)
    (list_poly_bound c.transformedCoeffs).2
    (bernstein_coeff_natAbs_le c.degreeBound c.bernsteinNumerators)
    h.b_bound
  rw [← intEval_eq, ← bernsteinEvalPair_eq bBase _ _ h.b_length]
  exact h.b_eval

theorem valid_spline_eval (c : Pure.CellData) (rBase bBase : ℤ)
    (h : Valid c rBase bBase) (x : ℝ) :
    ENT.Certificate.eval c.pCoeffs x = splinePiece c.n c.k x := by
  rw [h.spline, PureFast.fastSplineCoeffs_eq]
  exact fastSplineCoeffs_eval c.n c.k x

theorem valid_curvature_eval (c : Pure.CellData) (rBase bBase : ℤ)
    (h : Valid c rBase bBase) (x : ℝ) :
    ENT.Certificate.eval c.rCoeffs x = targetPolynomial c.n c.k x := by
  have heq := congrArg (fun p : Polynomial ℤ => p.eval₂ (Int.castRingHom ℝ) x)
    (valid_curvature_poly c rBase bBase h)
  rw [Block.eval₂_poly, Block.eval₂_poly] at heq
  rw [heq, Pure.curvature_eq]
  exact curvatureCoeffs_eval c.n c.k c.pCoeffs
    (valid_spline_eval c rBase bBase h) x

theorem valid_transformed_nonneg (c : Pure.CellData) (rBase bBase : ℤ)
    (h : Valid c rBase bBase) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ ENT.Certificate.eval c.transformedCoeffs x := by
  rw [← Block.eval₂_poly, valid_bernstein_poly c rBase bBase h]
  exact BlockBernstein.eval₂_bernsteinPolynomial_nonneg c.degreeBound c.bernsteinNumerators
    (by simpa only [List.all_eq_true, decide_eq_true_eq] using h.nonneg) x hx0 hx1

theorem valid_sound (c : Pure.CellData) (rBase bBase : ℤ)
    (h : Valid c rBase bBase) : CellConclusion (Pure.toSemanticData c) := by
  refine ⟨h.n_lower, h.n_upper, h.cell, h.half,
    valid_spline_eval c rBase bBase h, valid_curvature_eval c rBase bBase h, ?_⟩
  intro s hs0 hs1
  change 0 ≤ targetPolynomial c.n c.k s
  rw [← valid_curvature_eval c rBase bBase h s]
  have hnonneg := valid_transformed_nonneg c rBase bBase h
  cases hflag : c.halfCell with
  | false =>
      have ht : c.transformedCoeffs = c.rCoeffs := by simpa [hflag] using h.transform
      rw [ht] at hnonneg
      exact hnonneg s hs0 (by simpa [width, Pure.toSemanticData, hflag] using hs1)
  | true =>
      have ht : c.transformedCoeffs = Pure.halfTransform c.degreeBound c.rCoeffs := by
        simpa [hflag] using h.transform
      apply halfCell_nonneg (ENT.Certificate.eval c.rCoeffs)
        (ENT.Certificate.eval c.transformedCoeffs) ((2 : ℝ)^c.degreeBound)
        (pow_pos (by norm_num) _) ?_ hnonneg s hs0
        (by simpa [width, Pure.toSemanticData, hflag] using hs1)
      intro x
      rw [ht, Pure.halfTransform_eq]
      exact halfTransform_eval c.rCoeffs c.degreeBound h.r_length x

end
end ENT.Certificate.Kronecker
