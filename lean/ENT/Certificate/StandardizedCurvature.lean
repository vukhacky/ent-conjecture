module

public import ENT.Certificate.AffineLog
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-! Conversion from a nonnegative exact curvature polynomial to the local
standardized negative-log curvature inequality. This is a statement about
the explicit cell function; density identification is a separate theorem. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Certificate

noncomputable section

def standardizedCellCoordinate (n k : ℕ) (x : ℝ) : ℝ :=
  ((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2 - (k : ℝ)

def standardizedCellPotential (n k : ℕ) (x : ℝ) : ℝ :=
  affineLogPotential (splinePolynomial n k)
    (-(Real.sqrt (n : ℝ)) / 2) ((n : ℝ) / 2 - (k : ℝ)) x

theorem standardizedCellCoordinate_affine (n k : ℕ) (x : ℝ) :
    -(Real.sqrt (n : ℝ)) / 2 * x + ((n : ℝ) / 2 - (k : ℝ)) =
      standardizedCellCoordinate n k x := by
  unfold standardizedCellCoordinate
  ring

theorem third_deriv_standardizedCellPotential (n k : ℕ) (x : ℝ)
    (hp : splinePiece n k (standardizedCellCoordinate n k x) ≠ 0) :
    deriv (deriv (deriv (standardizedCellPotential n k))) x =
      (Real.sqrt (n : ℝ)) ^ 3 / 8 *
        (thirdLogNumerator (splinePiece n k) (standardizedCellCoordinate n k x) /
          (splinePiece n k (standardizedCellCoordinate n k x)) ^ 3) := by
  have hp' : (splinePolynomial n k).eval
      (-(Real.sqrt (n : ℝ)) / 2 * x + ((n : ℝ) / 2 - (k : ℝ))) ≠ 0 := by
    simpa only [standardizedCellCoordinate_affine, splinePolynomial_eval] using hp
  have h := third_deriv_affineLogPotential (splinePolynomial n k)
    (-(Real.sqrt (n : ℝ)) / 2) ((n : ℝ) / 2 - (k : ℝ)) x hp'
  have hfun : (fun y => (splinePolynomial n k).eval y) = splinePiece n k := by
    funext y
    exact splinePolynomial_eval n k y
  have hscale : -(-(Real.sqrt (n : ℝ)) / 2) ^ 3 =
      (Real.sqrt (n : ℝ)) ^ 3 / 8 := by ring
  rw [hscale] at h
  change deriv (deriv (deriv (affineLogPotential (splinePolynomial n k)
    (-(Real.sqrt (n : ℝ)) / 2) ((n : ℝ) / 2 - (k : ℝ))))) x = _
  rw [standardizedCellCoordinate_affine, logarithmicNumeratorPolynomial_eval,
    hfun, splinePolynomial_eval] at h
  exact h

theorem standardized_curvature_algebra (n delta p z : ℝ)
    (hn : 0 < n) (hp : 0 < p)
    (hr : 0 ≤ n ^ 3 * z - 56 * delta * p ^ 3) :
    (7 / n) * (delta / Real.sqrt n) ≤
      (Real.sqrt n) ^ 3 / 8 * (z / p ^ 3) := by
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hroot2 : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn.le
  have hrat : 56 * delta / n ^ 3 ≤ z / p ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hn 3) (pow_pos hp 3)).mpr
    nlinarith [hr]
  have hcoeff : (7 / n) * (delta / Real.sqrt n) =
      (Real.sqrt n) ^ 3 / 8 * (56 * delta / n ^ 3) := by
    have hroot4 : (Real.sqrt n) ^ 4 = n ^ 2 := by
      calc
        (Real.sqrt n) ^ 4 = ((Real.sqrt n) ^ 2) ^ 2 := by ring
        _ = n ^ 2 := by rw [hroot2]
    field_simp [ne_of_gt hn, ne_of_gt hroot]
    rw [hroot4]
    ring
  rw [hcoeff]
  exact mul_le_mul_of_nonneg_left hrat (by positivity)

theorem standardizedCellPotential_curvature_lower (n k : ℕ) (x : ℝ)
    (hn : 0 < n)
    (hp : 0 < splinePiece n k (standardizedCellCoordinate n k x))
    (hr : 0 ≤ targetPolynomial n k (standardizedCellCoordinate n k x)) :
    (7 / (n : ℝ)) * x ≤
      deriv (deriv (deriv (standardizedCellPotential n k))) x := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hroot : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hn'
  rw [third_deriv_standardizedCellPotential n k x (ne_of_gt hp)]
  have hcoord : ((n : ℝ) - 2 * (k : ℝ) -
      2 * standardizedCellCoordinate n k x) / Real.sqrt (n : ℝ) = x := by
    unfold standardizedCellCoordinate
    field_simp [hroot]
    ring
  have h := standardized_curvature_algebra (n : ℝ)
    ((n : ℝ) - 2 * (k : ℝ) - 2 * standardizedCellCoordinate n k x)
    (splinePiece n k (standardizedCellCoordinate n k x))
    (thirdLogNumerator (splinePiece n k) (standardizedCellCoordinate n k x))
    hn' hp hr
  simpa only [hcoord] using h

end
end ENT.Certificate
