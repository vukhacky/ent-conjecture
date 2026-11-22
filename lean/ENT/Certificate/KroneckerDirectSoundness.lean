module

public import ENT.Certificate.KroneckerDirectCore
public import ENT.Certificate.KroneckerSplineSoundness
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! The spline curvature determines the missing curvature coefficients of a direct cell certificate. The reconstructed coefficients satisfy the packed checker. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace ENT.Certificate.KroneckerDirect
noncomputable section
open Kronecker

private theorem curvature_bound_of_degree (n k d : ℕ) (p : List ℤ)
    (hp : CoeffBound (Block.poly p) d (sumAbs p)) :
    CoeffBound (Block.poly (Pure.curvatureCoeffs n k p)) (3 * d + 1)
      (curvatureCoeffBound n k d (sumAbs p)) := by
  let M := sumAbs p
  let P := Block.poly p
  let B := tripleFactor d * d ^ 3 * M ^ 3
  let T := tripleFactor d * M ^ 3
  have hd : CoeffBound P.derivative d (d * M) := hp.derivative
  have he : CoeffBound P.derivative.derivative d (d ^ 2 * M) := by
    convert hd.derivative using 1 <;> ring
  have hf : CoeffBound P.derivative.derivative.derivative d (d ^ 3 * M) := by
    convert he.derivative using 1 <;> ring
  have h1 : CoeffBound (P ^ 2 * P.derivative.derivative.derivative) (3 * d) B := by
    convert hp.triple hp hf using 1 <;> (try dsimp [B]) <;> ring
  have h2 : CoeffBound (P * P.derivative * P.derivative.derivative) (3 * d) B := by
    convert hp.triple hd he using 1 <;> (try dsimp [B]) <;> ring
  have h3 : CoeffBound (P.derivative ^ 3) (3 * d) B := by
    convert hd.cube using 1 <;> (try dsimp [B]) <;> ring
  have hlog : CoeffBound
      (P ^ 2 * P.derivative.derivative.derivative -
        C 3 * (P * P.derivative * P.derivative.derivative) + C 2 * P.derivative ^ 3)
      (3 * d) (6 * B) := by
    convert (h1.sub (h2.scale 3)).add (h3.scale 2) using 1 <;> norm_num <;> ring
  have hcube : CoeffBound (P ^ 3) (3 * d) T := hp.cube
  have hn3 : CoeffBound
      (C ((n : ℤ) ^ 3) * (P ^ 2 * P.derivative.derivative.derivative -
        C 3 * (P * P.derivative * P.derivative.derivative) + C 2 * P.derivative ^ 3))
      (3 * d + 1) (n ^ 3 * (6 * B)) := by
    have h := (hlog.scale ((n : ℤ) ^ 3)).mono (Nat.le_succ _) le_rfl
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h
    exact h
  have hnk : (56 * ((n : ℤ) - 2 * (k : ℤ))).natAbs ≤ 56 * (n + 2 * k) := by
    simpa [Int.natAbs_mul] using
      Nat.mul_le_mul_left 56 (Int.natAbs_sub_le (n : ℤ) (2 * (k : ℤ)))
  have hconstant : CoeffBound (C (56 * ((n : ℤ) - 2 * (k : ℤ))) * P ^ 3)
      (3 * d + 1) ((56 * (n + 2 * k)) * T) :=
    (hcube.scale_le _ _ hnk).mono (Nat.le_succ _) le_rfl
  have hlinear : CoeffBound (C 112 * (X * P ^ 3)) (3 * d + 1) (112 * T) := by
    simpa using hcube.X_mul.scale 112
  have heq : Block.poly (Pure.curvatureCoeffs n k p) =
      C ((n : ℤ) ^ 3) * (P ^ 2 * P.derivative.derivative.derivative -
        C 3 * (P * P.derivative * P.derivative.derivative) + C 2 * P.derivative ^ 3) -
      C (56 * ((n : ℤ) - 2 * (k : ℤ))) * P ^ 3 + C 112 * (X * P ^ 3) := by
    dsimp [P]
    simp only [Pure.curvatureCoeffs, Pure.logarithmicNumeratorCoeffs,
      Block.poly_add, Block.poly_scale, Block.poly_mul, Block.poly_power,
      Block.poly_derivative, Block.poly_cons, Block.poly_nil,
      map_zero, mul_zero, add_zero, map_mul, map_sub, map_neg, map_ofNat]
    ring
  rw [heq]
  convert (hn3.sub hconstant).add hlinear using 1 <;>
    (try dsimp [curvatureCoeffBound, B, T, M]) <;> ring

private theorem curvature_natDegree_le (c : CellData) (hn : 1 ≤ c.n)
    (hp : c.pCoeffs.length = c.n) (hD : c.degreeBound = 3 * c.n - 2) :
    (Block.poly (Pure.curvatureCoeffs c.n c.k c.pCoeffs)).natDegree ≤ c.degreeBound := by
  have hdeg : (Block.poly c.pCoeffs).natDegree ≤ c.n - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [Block.coeff_poly, Block.coeff_zero_of_length_le _ i (by omega)]
  have h := (curvature_bound_of_degree c.n c.k (c.n - 1) c.pCoeffs
    ⟨hdeg, (list_poly_bound c.pCoeffs).2⟩).1
  have heq : 3 * (c.n - 1) + 1 = c.degreeBound := by omega
  simpa only [heq] using h

def canonicalR (c : CellData) : List ℤ :=
  List.ofFn (fun i : Fin (c.degreeBound + 1) =>
    (Block.poly (Pure.curvatureCoeffs c.n c.k c.pCoeffs)).coeff i)

def canonicalQ (c : CellData) : List ℤ :=
  if c.halfCell then Pure.halfTransform c.degreeBound (canonicalR c) else canonicalR c

@[simp] theorem canonicalR_length (c : CellData) :
    (canonicalR c).length = c.degreeBound + 1 := by simp [canonicalR]

theorem canonicalR_poly (c : CellData) (hn : 1 ≤ c.n)
    (hp : c.pCoeffs.length = c.n) (hD : c.degreeBound = 3 * c.n - 2) :
    Block.poly (canonicalR c) = Block.poly (Pure.curvatureCoeffs c.n c.k c.pCoeffs) := by
  ext i
  rw [Block.coeff_poly]
  by_cases hi : i < c.degreeBound + 1
  · simp only [canonicalR, Block.coeff, List.getElem?_ofFn, dif_pos hi, Option.getD_some]
  · rw [Block.coeff_zero_of_length_le _ i (by rw [canonicalR_length]; omega)]
    exact (coeff_eq_zero_of_natDegree_lt ((curvature_natDegree_le c hn hp hD).trans_lt
      (by omega))).symm

private theorem sumAbs_le_length_mul (p : List ℤ) (M : ℕ)
    (h : ∀ a ∈ p, a.natAbs ≤ M) : sumAbs p ≤ p.length * M := by
  induction p with
  | nil => simp [sumAbs]
  | cons a p ih =>
      have ha := h a (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      change a.natAbs + sumAbs p ≤ (p.length + 1) * M
      calc
        _ ≤ M + p.length * M := Nat.add_le_add ha ht
        _ = _ := by ring

theorem canonicalR_sumAbs (c : CellData) :
    sumAbs (canonicalR c) ≤ (c.degreeBound + 1) * rCoeffBound c := by
  rw [← canonicalR_length c]
  apply sumAbs_le_length_mul
  intro a ha
  rcases List.mem_ofFn.mp ha with ⟨i, rfl⟩
  exact curvature_coeff_natAbs_le c.n c.k c.pCoeffs i

private theorem sumAbs_halfTransform_le (d : ℕ) (p : List ℤ) :
    sumAbs (Pure.halfTransform d p) ≤ 2 ^ d * sumAbs p := by
  induction p generalizing d with
  | nil => simp [Pure.halfTransform, sumAbs]
  | cons a p ih =>
      change ((2 : ℤ) ^ d * a).natAbs + sumAbs (Pure.halfTransform (d - 1) p) ≤
        2 ^ d * (a.natAbs + sumAbs p)
      rw [Int.natAbs_mul, Int.natAbs_pow]
      change 2 ^ d * a.natAbs + sumAbs (Pure.halfTransform (d - 1) p) ≤
        2 ^ d * (a.natAbs + sumAbs p)
      have hpow : 2 ^ (d - 1) ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) (Nat.sub_le d 1)
      calc
        _ ≤ 2 ^ d * a.natAbs + 2 ^ (d - 1) * sumAbs p := Nat.add_le_add_left (ih (d - 1)) _
        _ ≤ 2 ^ d * a.natAbs + 2 ^ d * sumAbs p :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hpow) _
        _ = _ := by ring

theorem canonicalQ_sumAbs (c : CellData) :
    sumAbs (canonicalQ c) ≤ (c.degreeBound + 1) * qCoeffBound c := by
  cases hf : c.halfCell with
  | false => simpa [canonicalQ, qCoeffBound, hf] using canonicalR_sumAbs c
  | true =>
      have h := (sumAbs_halfTransform_le c.degreeBound (canonicalR c)).trans
        (Nat.mul_le_mul_left (2 ^ c.degreeBound) (canonicalR_sumAbs c))
      simpa [canonicalQ, qCoeffBound, hf, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

private theorem intEval_halfTransform_twice (p : List ℤ) (d : ℕ)
    (hlen : p.length ≤ d + 1) (u : ℤ) :
    Kronecker.intEval (2 * u) (Pure.halfTransform d p) =
      (2 : ℤ) ^ d * Kronecker.intEval u p := by
  induction p generalizing d with
  | nil => simp [Pure.halfTransform, Kronecker.intEval]
  | cons a p ih =>
      cases d with
      | zero =>
          have hp : p = [] := by
            cases p with
            | nil => rfl
            | cons b q => simp only [List.length_cons] at hlen; omega
          simp [hp, Pure.halfTransform, Kronecker.intEval]
      | succ d =>
          have hp : p.length ≤ d + 1 := by simp only [List.length_cons] at hlen; omega
          simp only [Pure.halfTransform, Kronecker.intEval, Nat.add_sub_cancel,
            ih d hp, pow_succ]
          ring

theorem canonicalR_eval (c : CellData) (hn : 1 ≤ c.n)
    (hp : c.pCoeffs.length = c.n) (hD : c.degreeBound = 3 * c.n - 2) (x : ℤ) :
    Kronecker.intEval x (canonicalR c) = Kronecker.curvatureEval c.n c.k c.pCoeffs x := by
  rw [Kronecker.intEval_eq, canonicalR_poly c hn hp hD,
    ← Kronecker.intEval_eq, Kronecker.intEval_curvature]

theorem canonicalQ_eval (c : CellData) (hn : 1 ≤ c.n)
    (hp : c.pCoeffs.length = c.n) (hD : c.degreeBound = 3 * c.n - 2) (u : ℤ) :
    Kronecker.intEval (evaluationBase c u) (canonicalQ c) =
      transformScale c * Kronecker.curvatureEval c.n c.k c.pCoeffs u := by
  cases hf : c.halfCell with
  | false => simpa [canonicalQ, evaluationBase, transformScale, hf] using canonicalR_eval c hn hp hD u
  | true =>
      have hx := intEval_halfTransform_twice (canonicalR c) c.degreeBound
        (canonicalR_length c).le u
      rw [canonicalR_eval c hn hp hD u] at hx
      simpa [canonicalQ, evaluationBase, transformScale, hf] using hx

def toPureCell (c : CellData) : Pure.CellData where
  n := c.n
  k := c.k
  degreeBound := c.degreeBound
  halfCell := c.halfCell
  pCoeffs := c.pCoeffs
  rCoeffs := canonicalR c
  transformedCoeffs := canonicalQ c
  bernsteinNumerators := c.bernsteinNumerators

def reconstructionBase (c : CellData) : ℤ :=
  (sumAbs (canonicalR c) + rCoeffBound c + 1 : ℕ)

theorem valid_to_pure (c : CellData) (pBase u : ℤ) (h : Valid c pBase u) :
    Kronecker.Valid (toPureCell c) (reconstructionBase c) (evaluationBase c u) := by
  have hn : 1 ≤ c.n := by have := h.n_lower; omega
  refine {
    n_lower := h.n_lower
    n_upper := h.n_upper
    cell := h.cell
    half := h.half
    degree := h.degree.le
    r_length := ?_
    spline := ?_
    r_bound := ?_
    r_eval := ?_
    transform := rfl
    b_length := h.b_length
    b_bound := ?_
    b_eval := ?_
    nonneg := h.nonneg }
  · exact (canonicalR_length c).le
  · simpa only [toPureCell, KroneckerLite.fastSplineCoeffs_eq] using
      KroneckerSpline.checked_spline_eq c.n c.k c.pCoeffs pBase hn h.p_length h.p_bound h.p_eval
  · change sumAbs (canonicalR c) + curvatureCoeffBound c.n c.k c.pCoeffs.length
        (sumAbs c.pCoeffs) < (reconstructionBase c).natAbs
    rw [reconstructionBase, Int.natAbs_natCast]
    change sumAbs (canonicalR c) + rCoeffBound c < sumAbs (canonicalR c) + rCoeffBound c + 1
    omega
  · exact canonicalR_eval c hn h.p_length h.degree (reconstructionBase c)
  · exact lt_of_le_of_lt (Nat.add_le_add_right (canonicalQ_sumAbs c) _) h.b_bound
  · change Kronecker.intEval (evaluationBase c u) (canonicalQ c) =
      (Kronecker.bernsteinEvalPair (evaluationBase c u) c.bernsteinNumerators).2
    rw [canonicalQ_eval c hn h.p_length h.degree u]
    simpa only [KroneckerLite.bernsteinEvalPair_eq, KroneckerLite.curvatureEval_eq] using h.direct_eval.symm

theorem exists_valid_to_pure {n k : ℕ}
    (h : ∃ c : CellData, c.n = n ∧ c.k = k ∧
      ∃ pBase u : ℤ, Valid c pBase u) :
    ∃ c : Pure.CellData, c.n = n ∧ c.k = k ∧
      ∃ rBase bBase : ℤ, Kronecker.Valid c rBase bBase := by
  rcases h with ⟨c, hn, hk, pBase, u, hc⟩
  exact ⟨toPureCell c, hn, hk, reconstructionBase c, evaluationBase c u,
    valid_to_pure c pBase u hc⟩

theorem valid_sound (c : CellData) (pBase u : ℤ) (h : Valid c pBase u) :
    CellConclusion (Pure.toSemanticData (toPureCell c)) :=
  Kronecker.valid_sound (toPureCell c) (reconstructionBase c) (evaluationBase c u)
    (valid_to_pure c pBase u h)

end
end ENT.Certificate.KroneckerDirect
