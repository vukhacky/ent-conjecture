module

public import ENT.Certificate.KroneckerSplineCore
public import ENT.Certificate.KroneckerLiteSoundness
public import ENT.Certificate.BlockSplineCoefficients
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Bounded integer coefficients and the length guard recover the canonical spline from its value at a sufficiently large base. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Certificate.KroneckerSpline
noncomputable section

private theorem intEval_ofFn {n : ℕ} (f : Fin n → ℤ) (x : ℤ) :
    KroneckerLite.intEval x (List.ofFn f) = ∑ i : Fin n, f i * x ^ (i : ℕ) := by
  induction n with
  | zero => simp [KroneckerLite.intEval]
  | succ n ih =>
      rw [List.ofFn_succ, KroneckerLite.intEval, Fin.sum_univ_succ, ih]
      simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem intEval_add (x : ℤ) (p q : KroneckerLite.IntPoly) :
    KroneckerLite.intEval x (KroneckerLite.Dense.add p q) =
      KroneckerLite.intEval x p + KroneckerLite.intEval x q := by
  simpa only [KroneckerLite.intEval_eq, KroneckerLite.dense_add_eq] using
    Kronecker.intEval_add x p q

private theorem intEval_scale (x a : ℤ) (p : KroneckerLite.IntPoly) :
    KroneckerLite.intEval x (KroneckerLite.Dense.scale a p) =
      a * KroneckerLite.intEval x p := by
  simpa only [KroneckerLite.intEval_eq, KroneckerLite.dense_scale_eq] using
    Kronecker.intEval_scale x a p

private theorem intEval_binomial (a : ℤ) (m : ℕ) (x : ℤ) :
    KroneckerLite.intEval x (KroneckerLite.binomialPowerCoeffs a m) = (a + x) ^ m := by
  rw [KroneckerLite.binomialPowerCoeffs, intEval_ofFn, add_comm a x, add_pow,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [KroneckerLite.fastChoose_eq, ← Nat.choose_eq_fast_choose]
  ring

theorem intEval_fastSplineAux (n k m : ℕ) (x : ℤ) :
    KroneckerLite.intEval x (KroneckerLite.fastSplineCoeffsAux n k m) =
      canonicalEvalAux n k x m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [KroneckerLite.fastSplineCoeffsAux, intEval_add, ih, intEval_scale,
        intEval_binomial, canonicalEvalAux]
      congr 2
      congr 1
      ring

theorem intEval_fastSpline (n k : ℕ) (x : ℤ) :
    KroneckerLite.intEval x (KroneckerLite.fastSplineCoeffs n k) =
      canonicalEval n k x := intEval_fastSplineAux n k (k + 1) x

theorem directSplineCoeff_natAbs_le (n k i : ℕ) :
    (Block.directSplineCoeff n k i).natAbs ≤ canonicalCoeffBound n k := by
  unfold Block.directSplineCoeff
  simp only [← Nat.choose_eq_fast_choose, Int.natAbs_mul, Int.natAbs_natCast]
  have hsum :
      (∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (n.choose j : ℤ) *
        ((k : ℤ) - (j : ℤ)) ^ (n - 1 - i)).natAbs ≤
      (k + 1) * (2 ^ n * (k + 1) ^ (n - 1)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (k + 1),
          ((-1 : ℤ) ^ j * (n.choose j : ℤ) *
            ((k : ℤ) - (j : ℤ)) ^ (n - 1 - i)).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (k + 1), 2 ^ n * (k + 1) ^ (n - 1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
        simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
          one_pow, one_mul, Int.natAbs_natCast,
          Int.natAbs_natCast_sub_natCast_of_ge hjk]
        apply Nat.mul_le_mul (Nat.choose_le_two_pow n j)
        exact (Nat.pow_le_pow_left (by omega : k - j ≤ k + 1) _).trans
          (Nat.pow_le_pow_right (by omega : 0 < k + 1) (Nat.sub_le (n - 1) i))
      _ = _ := by simp
  have hconvert := List.sum_toFinset
    (fun j : ℕ => (-1 : ℤ) ^ j * (n.choose j : ℤ) *
      ((k : ℤ) - (j : ℤ)) ^ (n - 1 - i))
    (List.nodup_range (n := k + 1))
  simp only [List.toFinset_range] at hconvert
  rw [← hconvert]
  calc
    _ ≤ 2 ^ (n - 1) * ((k + 1) * (2 ^ n * (k + 1) ^ (n - 1))) :=
      Nat.mul_le_mul (Nat.choose_le_two_pow (n - 1) i) hsum
    _ = canonicalCoeffBound n k := by unfold canonicalCoeffBound; ring

theorem canonical_poly_coeff_bound (n k : ℕ) (hn : 1 ≤ n) (i : ℕ) :
    ((Block.poly (KroneckerLite.fastSplineCoeffs n k)).coeff i).natAbs ≤
      canonicalCoeffBound n k := by
  rw [KroneckerLite.fastSplineCoeffs_eq, Block.coeff_poly]
  by_cases hi : i < n
  · rw [Block.coeff_fastSplineCoeffs n k i hn hi]
    exact directSplineCoeff_natAbs_le n k i
  · rw [Block.coeff_zero_of_length_le _ i (by rw [Block.length_fastSplineCoeffs n k hn]; omega)]
    exact Nat.zero_le _

theorem checked_spline_eq (n k : ℕ) (p : KroneckerLite.IntPoly) (base : ℤ)
    (hn : 1 ≤ n) (hp : p.length = n)
    (hbound : KroneckerLite.sumAbs p + canonicalCoeffBound n k < base.natAbs)
    (heval : KroneckerLite.intEval base p = canonicalEval n k base) :
    p = KroneckerLite.fastSplineCoeffs n k := by
  have hpoly : Block.poly p = Block.poly (KroneckerLite.fastSplineCoeffs n k) := by
    apply Kronecker.eq_of_eval_eq_of_coeff_bounds _ _ base
      (KroneckerLite.sumAbs p) (canonicalCoeffBound n k)
      (Kronecker.list_poly_bound p).2 (canonical_poly_coeff_bound n k hn) hbound
    simpa only [← Kronecker.intEval_eq, ← KroneckerLite.intEval_eq,
      intEval_fastSpline] using heval
  rw [KroneckerLite.fastSplineCoeffs_eq] at hpoly ⊢
  apply Block.fastSplineCoeffs_eq_of_coefficients n k p hn hp
  intro i hi
  have h := congrArg (fun q : Polynomial ℤ => q.coeff i) hpoly
  simpa only [Block.coeff_poly, Block.coeff_fastSplineCoeffs n k i hn hi] using h

theorem valid_to_lite (c : CellData) (pBase rBase bBase : ℤ)
    (h : Valid c pBase rBase bBase) : KroneckerLite.Valid c rBase bBase where
  n_lower := h.n_lower
  n_upper := h.n_upper
  cell := h.cell
  half := h.half
  degree := h.degree
  r_length := h.r_length
  spline := checked_spline_eq c.n c.k c.pCoeffs pBase (by have := h.n_lower; omega)
    h.p_length h.p_bound h.p_eval
  r_bound := h.r_bound
  r_eval := h.r_eval
  transform := h.transform
  b_length := h.b_length
  b_bound := h.b_bound
  b_eval := h.b_eval
  nonneg := h.nonneg

theorem exists_valid_to_lite {n k : ℕ}
    (h : ∃ c : CellData, c.n = n ∧ c.k = k ∧
      ∃ pBase rBase bBase : ℤ, Valid c pBase rBase bBase) :
    ∃ c : KroneckerLite.CellData, c.n = n ∧ c.k = k ∧
      ∃ rBase bBase : ℤ, KroneckerLite.Valid c rBase bBase := by
  rcases h with ⟨c, hn, hk, pBase, rBase, bBase, hc⟩
  exact ⟨c, hn, hk, rBase, bBase, valid_to_lite c pBase rBase bBase hc⟩

theorem exists_valid_to_pure {n k : ℕ}
    (h : ∃ c : CellData, c.n = n ∧ c.k = k ∧
      ∃ pBase rBase bBase : ℤ, Valid c pBase rBase bBase) :
    ∃ c : Pure.CellData, c.n = n ∧ c.k = k ∧
      ∃ rBase bBase : ℤ, Kronecker.Valid c rBase bBase :=
  KroneckerLite.exists_valid_to_pure (exists_valid_to_lite h)

theorem valid_sound (c : CellData) (pBase rBase bBase : ℤ)
    (h : Valid c pBase rBase bBase) :
    CellConclusion (Pure.toSemanticData (KroneckerLite.toPureCell c)) :=
  KroneckerLite.valid_sound c rBase bBase (valid_to_lite c pBase rBase bBase h)

end
end ENT.Certificate.KroneckerSpline
