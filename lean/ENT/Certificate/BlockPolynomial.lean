module

public import ENT.Certificate.BlockCore
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Tactic.Ring

/-! Integer-polynomial semantics of the coefficient-block checks. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Certificate.Block

open ENT.Certificate.Pure Polynomial

def poly (p : IntPoly) : Polynomial ℤ :=
  Polynomial.ofFn p.length (fun i => p[i])

@[simp] theorem coeff_poly (p : IntPoly) (i : ℕ) : (poly p).coeff i = coeff p i := by
  unfold poly
  by_cases hi : i < p.length
  · simp [coeff, hi]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi)]
    simp [coeff, List.getElem?_eq_none (Nat.le_of_not_gt hi)]

theorem coeff_zero_of_length_le (p : IntPoly) (i : ℕ) (h : p.length ≤ i) :
    coeff p i = 0 := by
  simp [coeff, List.getElem?_eq_none h]

@[simp] theorem poly_nil : poly [] = 0 := by
  ext i
  simp [coeff_poly, coeff]

@[simp] theorem poly_cons (a : ℤ) (p : IntPoly) :
    poly (a :: p) = C a + X * poly p := by
  ext i
  cases i with
  | zero => simp [coeff_poly, coeff]
  | succ i =>
      rw [Polynomial.coeff_add, Polynomial.coeff_C]
      simp [coeff_poly, coeff, Polynomial.coeff_X_mul]

theorem poly_add (p q : IntPoly) : poly (Pure.Dense.add p q) = poly p + poly q := by
  induction p generalizing q with
  | nil => simp [Pure.Dense.add]
  | cons a p ih =>
      cases q with
      | nil => simp [Pure.Dense.add]
      | cons b q => simp only [Pure.Dense.add, poly_cons, ih, map_add]; ring

theorem poly_scale (a : ℤ) (p : IntPoly) : poly (Pure.Dense.scale a p) = C a * poly p := by
  induction p with
  | nil => simp [Pure.Dense.scale]
  | cons b p ih =>
      simp only [Pure.Dense.scale, List.map_cons, poly_cons, map_mul] at *
      rw [ih]
      ring

theorem poly_mul (p q : IntPoly) : poly (Pure.Dense.mul p q) = poly p * poly q := by
  induction p with
  | nil => simp [Pure.Dense.mul]
  | cons a p ih =>
      simp only [Pure.Dense.mul, poly_add, poly_scale, poly_cons, map_zero, zero_add, ih]
      ring

theorem poly_power (p : IntPoly) (n : ℕ) : poly (Pure.Dense.power p n) = poly p ^ n := by
  induction n with
  | zero => simp [Pure.Dense.power]
  | succ n ih => simp [Pure.Dense.power, poly_mul, ih, pow_succ, mul_comm]

theorem poly_derivative (p : IntPoly) :
    poly (Pure.Dense.derivative p) = (poly p).derivative := by
  induction p with
  | nil => simp [Pure.Dense.derivative]
  | cons a p ih =>
      cases p with
      | nil => simp [Pure.Dense.derivative]
      | cons b p =>
          simp only [Pure.Dense.derivative, poly_add, poly_cons, map_zero, zero_add,
            Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
            Polynomial.derivative_X, one_mul, zero_add] at *
          rw [← ih]

theorem convolutionCoeff_eq (p q : IntPoly) (i : ℕ) :
    convolutionCoeff p q i = ∑ j ∈ Finset.range (i + 1), coeff p j * coeff q (i - j) := by
  simpa only [convolutionCoeff, List.toFinset_range] using
    (List.sum_toFinset (fun j => coeff p j * coeff q (i - j))
      (List.nodup_range (n := i + 1))).symm

theorem coeff_poly_mul (p q : IntPoly) (i : ℕ) :
    (poly p * poly q).coeff i = convolutionCoeff p q i := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_poly, convolutionCoeff_eq]

theorem productValid_sound (p q r : IntPoly) (h : ProductValid p q r) :
    poly r = poly p * poly q := by
  rcases h with ⟨hlen, hcoeff⟩
  ext i
  rw [coeff_poly, coeff_poly_mul]
  by_cases hi : i < p.length + q.length
  · exact hcoeff i hi
  · rw [coeff_zero_of_length_le r i (by omega), convolutionCoeff_eq]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hp : p.length ≤ j
    · rw [coeff_zero_of_length_le p j hp, zero_mul]
    · have hq : q.length ≤ i - j := by omega
      rw [coeff_zero_of_length_le q (i - j) hq, mul_zero]

theorem derivativeValid_sound (p d : IntPoly) (h : DerivativeValid p d) :
    poly d = (poly p).derivative := by
  rcases h with ⟨hlen, hcoeff⟩
  ext i
  rw [coeff_poly, Polynomial.coeff_derivative, coeff_poly]
  by_cases hi : i < p.length
  · simpa [derivativeCoeff, mul_comm] using hcoeff i hi
  · rw [coeff_zero_of_length_le d i (by omega),
      coeff_zero_of_length_le p (i + 1) (by omega), zero_mul]

theorem linearValid_sound (n k d : ℕ) (w : Witness) (r : IntPoly)
    (h : LinearValid n k d w r) :
    poly r = C ((n : ℤ) ^ 3) * (poly w.a - C 3 * poly w.b + C 2 * poly w.c) -
      C (56 * ((n : ℤ) - 2 * (k : ℤ))) * poly w.t + C 112 * X * poly w.t := by
  rcases h with ⟨hrlen, halen, hblen, hclen, htlen, hcoeff⟩
  ext i
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    mul_assoc, coeff_poly]
  have hs : (X * poly w.t).coeff i = shiftedCoeff w.t i := by
    cases i <;> simp [shiftedCoeff, coeff_poly, Polynomial.coeff_X_mul]
  rw [hs]
  by_cases hi : i < d + 1
  · simpa [curvatureCoeff, mul_assoc] using hcoeff i hi
  · have hr : coeff r i = 0 := coeff_zero_of_length_le _ _ (by omega)
    have ha : coeff w.a i = 0 := coeff_zero_of_length_le _ _ (by omega)
    have hb : coeff w.b i = 0 := coeff_zero_of_length_le _ _ (by omega)
    have hc : coeff w.c i = 0 := coeff_zero_of_length_le _ _ (by omega)
    have ht : coeff w.t i = 0 := coeff_zero_of_length_le _ _ (by omega)
    have hshift : shiftedCoeff w.t i = 0 := by
      cases i with
      | zero => rfl
      | succ i => exact coeff_zero_of_length_le _ _ (by omega)
    simp [hr, ha, hb, hc, ht, hshift]

end ENT.Certificate.Block
