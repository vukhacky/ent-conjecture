module

public import ENT.Certificate.BlockPolynomial
public import ENT.Certificate.BernsteinCoefficients
public import ENT.Certificate.PureFastSoundness

/-! Soundness of the coefficient-block checks. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Certificate.Block

open ENT.Certificate.Pure Polynomial
noncomputable section

theorem eval₂_poly (p : Pure.IntPoly) (x : ℝ) :
    (poly p).eval₂ (Int.castRingHom ℝ) x = ENT.Certificate.eval p x := by
  induction p with
  | nil => simp
  | cons a p ih =>
      simp only [poly_cons, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X, ih, Dense.eval_cons]
      rfl

theorem bernsteinCoeff_eq (d : ℕ) (bs : Pure.IntPoly) (i : ℕ) :
    bernsteinCoeff d bs i = ∑ j ∈ Finset.range (i + 1),
      coeff bs j * (-1 : ℤ) ^ (i - j) * (Nat.choose (d - j) (i - j) : ℤ) := by
  rw [Nat.choose_eq_fast_choose]
  simpa only [bernsteinCoeff, List.toFinset_range] using
    (List.sum_toFinset (fun j => coeff bs j * (-1 : ℤ) ^ (i - j) *
      (Nat.fast_choose (d - j) (i - j) : ℤ)) (List.nodup_range (n := i + 1))).symm

theorem bernsteinValid_poly (d : ℕ) (q bs : Pure.IntPoly) (h : BernsteinValid d q bs) :
    poly q = BlockBernstein.bernsteinPolynomial d bs := by
  rcases h with ⟨hq, hbs, hc, hnonneg⟩
  ext i
  by_cases hi : i ≤ d
  · rw [coeff_poly, BlockBernstein.coeff_bernsteinPolynomial_of_le d bs i hi]
    simpa only [bernsteinCoeff_eq, coeff] using hc i (by omega)
  · rw [coeff_poly, coeff_zero_of_length_le q i (by omega),
      BlockBernstein.coeff_bernsteinPolynomial_eq_zero d bs i (by omega)]

theorem bernsteinValid_nonneg (d : ℕ) (q bs : Pure.IntPoly) (h : BernsteinValid d q bs)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ ENT.Certificate.eval q x := by
  rw [← eval₂_poly, bernsteinValid_poly d q bs h]
  exact BlockBernstein.eval₂_bernsteinPolynomial_nonneg d bs
    (by simpa only [List.all_eq_true, decide_eq_true_eq] using h.2.2.2) x hx0 hx1

theorem valid_curvature_poly (c : Pure.CellData) (w : Witness) (h : Valid c w) :
    poly c.rCoeffs = poly (Pure.curvatureCoeffs c.n c.k c.pCoeffs) := by
  have hd := derivativeValid_sound _ _ h.d_valid
  have he := derivativeValid_sound _ _ h.e_valid
  have hf := derivativeValid_sound _ _ h.f_valid
  have hq := productValid_sound _ _ _ h.q_valid
  have hu := productValid_sound _ _ _ h.u_valid
  have hv := productValid_sound _ _ _ h.v_valid
  have ht := productValid_sound _ _ _ h.t_valid
  have ha := productValid_sound _ _ _ h.a_valid
  have hb := productValid_sound _ _ _ h.b_valid
  have hc := productValid_sound _ _ _ h.c_valid
  rw [linearValid_sound _ _ _ _ _ h.r_valid]
  simp only [ha, hb, hc, ht, hq, hu, hv, hf, he, hd,
    Pure.curvatureCoeffs, Pure.logarithmicNumeratorCoeffs,
    poly_add, poly_scale, poly_mul, poly_power, poly_derivative, poly_cons, poly_nil,
    mul_zero, add_zero, map_mul, map_sub, map_neg, map_ofNat]
  ring

theorem valid_spline_eval (c : Pure.CellData) (w : Witness) (h : Valid c w) (x : ℝ) :
    ENT.Certificate.eval c.pCoeffs x = splinePiece c.n c.k x := by
  rw [h.spline, PureFast.fastSplineCoeffs_eq]
  exact fastSplineCoeffs_eval c.n c.k x

theorem valid_curvature_eval (c : Pure.CellData) (w : Witness) (h : Valid c w) (x : ℝ) :
    ENT.Certificate.eval c.rCoeffs x = targetPolynomial c.n c.k x := by
  have heq := congrArg (fun p : Polynomial ℤ => p.eval₂ (Int.castRingHom ℝ) x)
    (valid_curvature_poly c w h)
  rw [eval₂_poly, eval₂_poly] at heq
  rw [heq, Pure.curvature_eq]
  exact curvatureCoeffs_eval c.n c.k c.pCoeffs (valid_spline_eval c w h) x

theorem valid_sound (c : Pure.CellData) (w : Witness) (h : Valid c w) :
    CellConclusion (Pure.toSemanticData c) := by
  refine ⟨h.n_lower, h.n_upper, h.cell, h.half,
    valid_spline_eval c w h, valid_curvature_eval c w h, ?_⟩
  intro s hs0 hs1
  change 0 ≤ targetPolynomial c.n c.k s
  rw [← valid_curvature_eval c w h s]
  have hnonneg := bernsteinValid_nonneg c.degreeBound c.transformedCoeffs
    c.bernsteinNumerators h.bernstein
  cases hflag : c.halfCell with
  | false =>
      have ht : c.transformedCoeffs = c.rCoeffs := by simpa [hflag] using h.transform
      rw [ht] at hnonneg
      exact hnonneg s hs0 (by simpa [width, Pure.toSemanticData, hflag] using hs1)
  | true =>
      have ht : c.transformedCoeffs = Pure.halfTransform c.degreeBound c.rCoeffs := by
        simpa [hflag] using h.transform
      apply halfCell_nonneg (ENT.Certificate.eval c.rCoeffs)
        (ENT.Certificate.eval c.transformedCoeffs) ((2 : ℝ) ^ c.degreeBound)
        (pow_pos (by norm_num) _) ?_ hnonneg s hs0
        (by simpa [width, Pure.toSemanticData, hflag] using hs1)
      intro x
      rw [ht, Pure.halfTransform_eq]
      exact halfTransform_eval c.rCoeffs c.degreeBound h.r_valid.1 x

end
end ENT.Certificate.Block
