module

public import ENT.Certificate.PureFast
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Integer certificates for blocks of polynomial coefficients. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Certificate.Block

open Pure

def coeff (p : IntPoly) (i : ℕ) : ℤ := p[i]?.getD 0

def convolutionCoeff (p q : IntPoly) (i : ℕ) : ℤ :=
  ((List.range (i + 1)).map (fun j => coeff p j * coeff q (i - j))).sum

def derivativeCoeff (p : IntPoly) (i : ℕ) : ℤ := (i + 1 : ℕ) * coeff p (i + 1)

def shiftedCoeff (p : IntPoly) (i : ℕ) : ℤ :=
  match i with
  | 0 => 0
  | j + 1 => coeff p j

def bernsteinCoeff (d : ℕ) (bs : IntPoly) (i : ℕ) : ℤ :=
  ((List.range (i + 1)).map (fun j =>
    coeff bs j * (-1 : ℤ) ^ (i - j) * (Nat.fast_choose (d - j) (i - j) : ℤ))).sum

def checkBlock (start count : ℕ) (p : ℕ → Prop) [DecidablePred p] : Bool :=
  (List.range count).all (fun j => decide (p (start + j)))

theorem checkBlock_sound {start count : ℕ} {p : ℕ → Prop} [DecidablePred p]
    (h : checkBlock start count p = true) (i : ℕ)
    (hi0 : start ≤ i) (hi1 : i < start + count) : p i := by
  have hm : i - start ∈ List.range count := List.mem_range.mpr (by omega)
  have hp := List.all_eq_true.mp h (i - start) hm
  have heq : start + (i - start) = i := by omega
  simpa only [heq, decide_eq_true_eq] using hp

def DerivativeValid (p d : IntPoly) : Prop :=
  d.length ≤ p.length ∧
    ∀ i : ℕ, i < p.length → coeff d i = derivativeCoeff p i

def ProductValid (p q r : IntPoly) : Prop :=
  r.length ≤ p.length + q.length ∧
    ∀ i : ℕ, i < p.length + q.length → coeff r i = convolutionCoeff p q i

structure Witness where
  d : IntPoly
  e : IntPoly
  f : IntPoly
  q : IntPoly
  u : IntPoly
  v : IntPoly
  t : IntPoly
  a : IntPoly
  b : IntPoly
  c : IntPoly

def curvatureCoeff (n k : ℕ) (w : Witness) (i : ℕ) : ℤ :=
  (n : ℤ) ^ 3 * (coeff w.a i - 3 * coeff w.b i + 2 * coeff w.c i) -
    56 * ((n : ℤ) - 2 * (k : ℤ)) * coeff w.t i + 112 * shiftedCoeff w.t i

def LinearValid (n k d : ℕ) (w : Witness) (r : IntPoly) : Prop :=
  r.length ≤ d + 1 ∧ w.a.length ≤ d + 1 ∧ w.b.length ≤ d + 1 ∧
    w.c.length ≤ d + 1 ∧ w.t.length ≤ d ∧
      ∀ i : ℕ, i < d + 1 → coeff r i = curvatureCoeff n k w i

def BernsteinValid (d : ℕ) (q bs : IntPoly) : Prop :=
  q.length ≤ d + 1 ∧ bs.length = d + 1 ∧
    (∀ i : ℕ, i < d + 1 → coeff q i = bernsteinCoeff d bs i) ∧
    bs.all (fun b => decide (0 ≤ b)) = true

structure Valid (c : Pure.CellData) (w : Witness) : Prop where
  n_lower : 7 ≤ c.n
  n_upper : c.n ≤ 149
  cell : 2 * c.k < c.n
  half : c.halfCell = true ↔ 2 * c.k + 1 = c.n
  degree : c.degreeBound ≤ 3 * c.n - 2
  spline : c.pCoeffs = PureFast.fastSplineCoeffs c.n c.k
  d_valid : DerivativeValid c.pCoeffs w.d
  e_valid : DerivativeValid w.d w.e
  f_valid : DerivativeValid w.e w.f
  q_valid : ProductValid c.pCoeffs c.pCoeffs w.q
  u_valid : ProductValid c.pCoeffs w.d w.u
  v_valid : ProductValid w.d w.d w.v
  t_valid : ProductValid w.q c.pCoeffs w.t
  a_valid : ProductValid w.q w.f w.a
  b_valid : ProductValid w.u w.e w.b
  c_valid : ProductValid w.v w.d w.c
  r_valid : LinearValid c.n c.k c.degreeBound w c.rCoeffs
  transform : c.transformedCoeffs =
    if c.halfCell then Pure.halfTransform c.degreeBound c.rCoeffs else c.rCoeffs
  bernstein : BernsteinValid c.degreeBound c.transformedCoeffs c.bernsteinNumerators

end ENT.Certificate.Block
