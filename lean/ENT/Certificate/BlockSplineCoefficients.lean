module

public import ENT.Certificate.BlockSplineCore
public import Mathlib.Tactic.Ring

/-! Coefficient identities for the block representation of the canonical spline. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Certificate.Block

open ENT.Certificate.Pure

private theorem spline_length_add (p q : IntPoly) :
    (Dense.add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [Dense.add]
  | cons a p ih =>
      cases q with
      | nil => simp [Dense.add]
      | cons b q => simp [Dense.add, ih]

private theorem spline_coeff_add (p q : IntPoly) (i : ℕ) :
    coeff (Dense.add p q) i = coeff p i + coeff q i := by
  induction p generalizing q i with
  | nil => simp [Dense.add, coeff]
  | cons a p ih =>
      cases q with
      | nil => simp [Dense.add, coeff]
      | cons b q =>
          cases i with
          | zero => simp [Dense.add, coeff]
          | succ i => simpa [Dense.add, coeff] using ih q i

private theorem spline_coeff_scale (a : ℤ) (p : IntPoly) (i : ℕ) :
    coeff (Dense.scale a p) i = a * coeff p i := by
  simp only [Dense.scale, coeff, List.getElem?_map]
  cases p[i]? <;> simp

private theorem spline_coeff_binomial (a : ℤ) (m i : ℕ) (hi : i < m + 1) :
    coeff (PureFast.binomialPowerCoeffs a m) i =
      (Nat.fast_choose m i : ℤ) * a ^ (m - i) := by
  simp only [coeff, PureFast.binomialPowerCoeffs, List.getElem?_ofFn, dif_pos hi,
    Option.getD_some]

private theorem spline_length_aux (n k m : ℕ) (hn : 1 ≤ n) :
    (PureFast.fastSplineCoeffsAux n k m).length = if m = 0 then 0 else n := by
  have hn' : n - 1 + 1 = n := by omega
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [PureFast.fastSplineCoeffsAux, spline_length_add, Dense.scale,
        List.length_map, PureFast.binomialPowerCoeffs, List.length_ofFn, hn', ih]
      cases m <;> simp

theorem length_fastSplineCoeffs (n k : ℕ) (hn : 1 ≤ n) :
    (PureFast.fastSplineCoeffs n k).length = n := by
  simpa [PureFast.fastSplineCoeffs] using spline_length_aux n k (k + 1) hn

private theorem spline_coeff_aux (n k m i : ℕ) (hn : 1 ≤ n) (hi : i < n) :
    coeff (PureFast.fastSplineCoeffsAux n k m) i =
      (Nat.fast_choose (n - 1) i : ℤ) *
        ((List.range m).map (fun j =>
          (-1 : ℤ) ^ j * (Nat.fast_choose n j : ℤ) *
            ((k : ℤ) - (j : ℤ)) ^ (n - 1 - i))).sum := by
  have hi' : i < n - 1 + 1 := by omega
  induction m with
  | zero => simp [PureFast.fastSplineCoeffsAux, coeff]
  | succ m ih =>
      rw [PureFast.fastSplineCoeffsAux, spline_coeff_add, spline_coeff_scale,
        spline_coeff_binomial _ _ _ hi', ih, List.range_succ,
        List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      ring

theorem coeff_fastSplineCoeffs (n k i : ℕ) (hn : 1 ≤ n) (hi : i < n) :
    coeff (PureFast.fastSplineCoeffs n k) i = directSplineCoeff n k i := by
  exact spline_coeff_aux n k (k + 1) i hn hi

theorem fastSplineCoeffs_eq_of_coefficients (n k : ℕ) (p : IntPoly)
    (hn : 1 ≤ n) (hp : p.length = n)
    (hc : ∀ i : ℕ, i < n → coeff p i = directSplineCoeff n k i) :
    p = PureFast.fastSplineCoeffs n k := by
  have hq := length_fastSplineCoeffs n k hn
  apply List.ext_getElem (hp.trans hq.symm)
  intro i hi hj
  have hi' : i < n := by omega
  have h := (hc i hi').trans (coeff_fastSplineCoeffs n k i hn hi').symm
  simpa only [coeff, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some] using h

end ENT.Certificate.Block
