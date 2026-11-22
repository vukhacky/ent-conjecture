module

public import ENT.Certificate.KroneckerBoundCore
public import ENT.Certificate.BlockPolynomial
public import ENT.Certificate.BernsteinCoefficients
public import Mathlib.Data.Nat.Choose.Bounds

/-! Bounds on integer coefficients for packed polynomial identity checks. -/

@[expose] public section
set_option autoImplicit false
open Polynomial
open scoped BigOperators

namespace ENT.Certificate.Kronecker

def CoeffBound (p : Polynomial ℤ) (d M : ℕ) : Prop :=
  p.natDegree ≤ d ∧ ∀ i : ℕ, (p.coeff i).natAbs ≤ M

namespace CoeffBound

variable {p q r : Polynomial ℤ} {d e M N K : ℕ}

theorem mono (hp : CoeffBound p d M) {e N : ℕ} (hd : d ≤ e) (hM : M ≤ N) :
    CoeffBound p e N :=
  ⟨hp.1.trans hd, fun i => (hp.2 i).trans hM⟩

theorem add (hp : CoeffBound p d M) (hq : CoeffBound q d N) :
    CoeffBound (p + q) d (M + N) := by
  refine ⟨(natDegree_add_le p q).trans (max_le hp.1 hq.1), ?_⟩
  intro i
  rw [coeff_add]
  exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (hp.2 i) (hq.2 i))

theorem sub (hp : CoeffBound p d M) (hq : CoeffBound q d N) :
    CoeffBound (p - q) d (M + N) := by
  refine ⟨(natDegree_sub_le p q).trans (max_le hp.1 hq.1), ?_⟩
  intro i
  rw [coeff_sub]
  exact (Int.natAbs_sub_le _ _).trans (Nat.add_le_add (hp.2 i) (hq.2 i))

theorem scale (hp : CoeffBound p d M) (a : ℤ) :
    CoeffBound (C a * p) d (a.natAbs * M) := by
  refine ⟨(natDegree_C_mul_le _ _).trans hp.1, ?_⟩
  intro i
  rw [coeff_C_mul, Int.natAbs_mul]
  exact Nat.mul_le_mul_left _ (hp.2 i)

theorem scale_le (hp : CoeffBound p d M) (a : ℤ) (A : ℕ) (ha : a.natAbs ≤ A) :
    CoeffBound (C a * p) d (A * M) :=
  (hp.scale a).mono le_rfl (Nat.mul_le_mul_right _ ha)

theorem X_mul (hp : CoeffBound p d M) : CoeffBound (X * p) (d + 1) M := by
  refine ⟨?_, ?_⟩
  · have h := (natDegree_mul_le (p := (X : Polynomial ℤ)) (q := p)).trans
      (Nat.add_le_add (show (X : Polynomial ℤ).natDegree ≤ 1 by simp) hp.1)
    omega
  · intro i
    cases i with
    | zero => simp
    | succ i => simpa only [coeff_X_mul] using hp.2 i

theorem derivative (hp : CoeffBound p d M) : CoeffBound p.derivative d (d * M) := by
  refine ⟨(natDegree_derivative_le p).trans ((Nat.sub_le _ _).trans hp.1), ?_⟩
  intro i
  rw [coeff_derivative, Int.natAbs_mul, ← Nat.cast_add_one, Int.natAbs_natCast]
  by_cases hi : i + 1 ≤ d
  · simpa only [Nat.mul_comm] using Nat.mul_le_mul (hp.2 (i + 1)) hi
  · rw [coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt (Nat.lt_of_not_ge hi))]
    simp

theorem mul (hp : CoeffBound p d M) (hq : CoeffBound q e N) :
    CoeffBound (p * q) (d + e) ((d + e + 1) * M * N) := by
  have hdeg : (p * q).natDegree ≤ d + e :=
    natDegree_mul_le.trans (Nat.add_le_add hp.1 hq.1)
  refine ⟨hdeg, ?_⟩
  intro i
  by_cases hi : i ≤ d + e
  · rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    calc
      (∑ j ∈ Finset.range (i + 1), p.coeff j * q.coeff (i - j)).natAbs
          ≤ ∑ j ∈ Finset.range (i + 1), (p.coeff j * q.coeff (i - j)).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (i + 1), M * N := by
        apply Finset.sum_le_sum
        intro j _
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (hp.2 j) (hq.2 (i - j))
      _ = (i + 1) * (M * N) := by simp
      _ ≤ (d + e + 1) * M * N := by
        simpa only [Nat.mul_assoc] using
          Nat.mul_le_mul_right (M * N) (Nat.succ_le_succ hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

theorem triple (hp : CoeffBound p d M) (hq : CoeffBound q d N)
    (hr : CoeffBound r d K) :
    CoeffBound (p * q * r) (3 * d) (tripleFactor d * M * N * K) := by
  have h := (hp.mul hq).mul hr
  convert h using 1 <;> (try dsimp [tripleFactor]) <;> ring

theorem cube (hp : CoeffBound p d M) :
    CoeffBound (p ^ 3) (3 * d) (tripleFactor d * M ^ 3) := by
  convert hp.triple hp hp using 1 <;> ring

end CoeffBound

theorem coeff_natAbs_le_sumAbs (p : List ℤ) (i : ℕ) :
    (Block.coeff p i).natAbs ≤ sumAbs p := by
  induction p generalizing i with
  | nil => simp [Block.coeff, sumAbs]
  | cons a p ih =>
      cases i with
      | zero => simp [Block.coeff, sumAbs]
      | succ i =>
          simpa only [Block.coeff, List.getElem?_cons_succ, sumAbs,
            List.map_cons, List.sum_cons] using
            (ih i).trans (Nat.le_add_left (sumAbs p) a.natAbs)

theorem list_poly_bound (p : List ℤ) :
    CoeffBound (Block.poly p) p.length (sumAbs p) := by
  refine ⟨natDegree_le_iff_coeff_eq_zero.mpr ?_, ?_⟩
  · intro i hi
    rw [Block.coeff_poly, Block.coeff_zero_of_length_le p i (by omega)]
  · intro i
    rw [Block.coeff_poly]
    exact coeff_natAbs_le_sumAbs p i

private theorem list_prefix_natAbs_le (p : List ℤ) (n : ℕ) :
    ((List.range n).map (fun i => (Block.coeff p i).natAbs)).sum ≤ sumAbs p := by
  induction p generalizing n with
  | nil => simp [Block.coeff, sumAbs]
  | cons a p ih =>
      cases n with
      | zero => simp [sumAbs]
      | succ n =>
          simp only [List.sum_range_succ', Block.coeff, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some, sumAbs, List.map_cons, List.sum_cons]
          exact Nat.add_le_add_left (ih n) _

theorem sum_range_coeff_natAbs_le (p : List ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (Block.coeff p i).natAbs) ≤ sumAbs p := by
  have he := List.sum_toFinset (fun i => (Block.coeff p i).natAbs)
    (List.nodup_range (n := n))
  simp only [List.toFinset_range] at he
  rw [he]
  exact list_prefix_natAbs_le p n

theorem bernstein_bound (D : ℕ) (bs : List ℤ) :
    CoeffBound (BlockBernstein.bernsteinPolynomial D bs) D (bernsteinCoeffBound D bs) := by
  refine ⟨BlockBernstein.natDegree_bernsteinPolynomial_le D bs, ?_⟩
  intro i
  by_cases hi : i ≤ D
  · rw [BlockBernstein.coeff_bernsteinPolynomial_of_le D bs i hi]
    calc
      (∑ j ∈ Finset.range (i + 1),
          bs[j]?.getD 0 * (-1 : ℤ) ^ (i - j) * (Nat.choose (D - j) (i - j) : ℤ)).natAbs
          ≤ ∑ j ∈ Finset.range (i + 1),
              (bs[j]?.getD 0 * (-1 : ℤ) ^ (i - j) * (Nat.choose (D - j) (i - j) : ℤ)).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (i + 1), (Block.coeff bs j).natAbs * 2 ^ D := by
        apply Finset.sum_le_sum
        intro j _
        simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
          one_pow, mul_one, Int.natAbs_natCast, Block.coeff]
        exact Nat.mul_le_mul_left _ ((Nat.choose_le_two_pow _ _).trans
          (Nat.pow_le_pow_right (by decide) (Nat.sub_le D j)))
      _ = (∑ j ∈ Finset.range (i + 1), (Block.coeff bs j).natAbs) * 2 ^ D :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ bernsteinCoeffBound D bs :=
        Nat.mul_le_mul_right _ (sum_range_coeff_natAbs_le bs (i + 1))
  · rw [BlockBernstein.coeff_bernsteinPolynomial_eq_zero D bs i (by omega)]
    simp

theorem curvature_bound (n k : ℕ) (p : List ℤ) :
    CoeffBound (Block.poly (Pure.curvatureCoeffs n k p)) (3 * p.length + 1)
      (curvatureCoeffBound n k p.length (sumAbs p)) := by
  let d := p.length
  let M := sumAbs p
  let P := Block.poly p
  let B := tripleFactor d * d ^ 3 * M ^ 3
  let T := tripleFactor d * M ^ 3
  have hp : CoeffBound P d M := list_poly_bound p
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
    (try dsimp [curvatureCoeffBound, B, T, d, M]) <;> ring

theorem curvature_coeff_natAbs_le (n k : ℕ) (p : List ℤ) (i : ℕ) :
    ((Block.poly (Pure.curvatureCoeffs n k p)).coeff i).natAbs ≤
      curvatureCoeffBound n k p.length (sumAbs p) :=
  (curvature_bound n k p).2 i

theorem bernstein_coeff_natAbs_le (D : ℕ) (bs : List ℤ) (i : ℕ) :
    ((BlockBernstein.bernsteinPolynomial D bs).coeff i).natAbs ≤ bernsteinCoeffBound D bs :=
  (bernstein_bound D bs).2 i

end ENT.Certificate.Kronecker
