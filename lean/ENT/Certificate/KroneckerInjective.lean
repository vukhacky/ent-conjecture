module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Int.Basic

/-! An integer evaluation base exceeding the coefficient bound gives injectivity on the bounded polynomials. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Certificate.Kronecker
open Polynomial

theorem eq_zero_of_eval_eq_zero_of_coeff_lt (p : Polynomial ℤ) (base : ℤ)
    (hbase : base ≠ 0) (heval : p.eval base = 0)
    (hcoeff : ∀ i : ℕ, (p.coeff i).natAbs < base.natAbs) : p = 0 := by
  induction p using Polynomial.recOnHorner with
  | M0 => rfl
  | MC p a hp0 ha ih =>
      have hd : base ∣ (p + C a).coeff 0 :=
        (show (p + C a).IsRoot base from heval).dvd_coeff_zero
      have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (hcoeff 0)
      have haz : a = 0 := by simpa only [coeff_add, coeff_C_zero, hp0, zero_add] using hz
      exact (ha haz).elim
  | MX p hp ih =>
      have he : p.eval base = 0 := by
        have hm : p.eval base * base = 0 := by simpa only [eval_mul, eval_X] using heval
        exact (mul_eq_zero.mp hm).resolve_right hbase
      have hc : ∀ i : ℕ, (p.coeff i).natAbs < base.natAbs := by
        intro i
        simpa only [coeff_mul_X] using hcoeff (i + 1)
      rw [ih he hc, zero_mul]

theorem eq_of_eval_eq_of_coeff_bounds (p q : Polynomial ℤ) (base : ℤ)
    (Mp Mq : ℕ) (hp : ∀ i : ℕ, (p.coeff i).natAbs ≤ Mp)
    (hq : ∀ i : ℕ, (q.coeff i).natAbs ≤ Mq)
    (hbase : Mp + Mq < base.natAbs) (heval : p.eval base = q.eval base) : p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_eq_zero_of_coeff_lt (p - q) base
  · intro hz
    simp only [hz, Int.natAbs_zero] at hbase
    exact Nat.not_lt_zero _ hbase
  · simpa only [eval_sub] using sub_eq_zero.mpr heval
  · intro i
    rw [coeff_sub]
    exact lt_of_le_of_lt ((Int.natAbs_sub_le _ _).trans (Nat.add_le_add (hp i) (hq i))) hbase

end ENT.Certificate.Kronecker
