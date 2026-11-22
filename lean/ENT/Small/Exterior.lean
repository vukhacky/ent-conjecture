module

public import ENT.Small.OcticParameters
public import ENT.Entropy.Scaling
public import ENT.Spline.DensityLaw
public import ENT.Basic.ProjectionDensity

/-! Entropy comparison away from the diagonal, using the octic partition function, moments, scaling and numerical slack bounds. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory

namespace ENT.Small
noncomputable section

def diagonalApproximationDefect (n : ℕ) (hn : 2 ≤ n) (W : ℝ → ℝ) : ℝ :=
  approximationDefect W ((Spline.diagonalFiniteEntropyDensity n hn).scale
    (Real.sqrt 3) (Real.sqrt_pos.mpr (by norm_num)))

theorem diagonalApproximationDefect_formula (n : ℕ) (hn : 2 ≤ n) (W : ℝ → ℝ) :
    diagonalApproximationDefect n hn W = Real.log (partitionFunction W) +
      (∫ x, W x ∂varianceOneProjectionLaw (diagonal n)) -
        (Spline.diagonalFiniteEntropyDensity n hn).entropy - Real.log (Real.sqrt 3) := by
  unfold diagonalApproximationDefect approximationDefect
  rw [FiniteEntropyDensity.entropy_scale]
  unfold varianceOneProjectionLaw
  ring

def sigma3 : ℝ := diagonalApproximationDefect 3 (by decide) W3
def sigma4 : ℝ := diagonalApproximationDefect 4 (by decide) W4
def sigma5 : ℝ := diagonalApproximationDefect 5 (by decide) W5
def sigma6 : ℝ := diagonalApproximationDefect 6 (by decide) W6

theorem entropy_gap_ge_octic_defect {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℝ) (ha : IsUnit a) (c₁ c₂ c₃ c₄ lam : ℝ)
    (hZ : Integrable (fun x => Real.exp (-octicPolynomial c₁ c₂ c₃ c₄ x)) volume)
    (hmoment : lam * deficit a ≤
      (∫ x, octicPolynomial c₁ c₂ c₃ c₄ x ∂varianceOneProjectionLaw (diagonal n)) -
      (∫ x, octicPolynomial c₁ c₂ c₃ c₄ x ∂varianceOneProjectionLaw a)) :
    lam * deficit a - diagonalApproximationDefect n hn (octicPolynomial c₁ c₂ c₃ c₄) ≤
      (Spline.diagonalFiniteEntropyDensity n hn).entropy -
        (projectionFiniteEntropyDensity a ha).entropy := by
  let p := projectionFiniteEntropyDensity a ha
  let q := Spline.diagonalFiniteEntropyDensity n hn
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h := entropy_gap_ge_potential_gap_sub_approximation
    (p.scale (Real.sqrt 3) h3) (q.scale (Real.sqrt 3) h3) hZ
    (octicPolynomial_integrable a c₁ c₂ c₃ c₄)
    (octicPolynomial_integrable (diagonal n) c₁ c₂ c₃ c₄)
  rw [p.entropy_scale, q.entropy_scale] at h
  change (∫ x, octicPolynomial c₁ c₂ c₃ c₄ x ∂varianceOneProjectionLaw (diagonal n)) -
      (∫ x, octicPolynomial c₁ c₂ c₃ c₄ x ∂varianceOneProjectionLaw a) -
        diagonalApproximationDefect n hn (octicPolynomial c₁ c₂ c₃ c₄) ≤
      q.entropy + Real.log (Real.sqrt 3) - (p.entropy + Real.log (Real.sqrt 3)) at h
  change lam * deficit a - diagonalApproximationDefect n hn (octicPolynomial c₁ c₂ c₃ c₄) ≤
    q.entropy - p.entropy
  linarith

theorem entropy_gap_three (a : Fin 3 → ℝ) (ha : IsUnit a) :
    (1 / 100 : ℝ) * deficit a - sigma3 ≤
      (Spline.diagonalFiniteEntropyDensity 3 (by decide)).entropy -
        (projectionFiniteEntropyDensity a ha).entropy :=
  entropy_gap_ge_octic_defect (by decide) a ha _ _ _ _ _ W3_exp_integrable (W3_moment_comparison a ha)

theorem entropy_gap_four (a : Fin 4 → ℝ) (ha : IsUnit a) :
    (11 / 1000 : ℝ) * deficit a - sigma4 ≤
      (Spline.diagonalFiniteEntropyDensity 4 (by decide)).entropy -
        (projectionFiniteEntropyDensity a ha).entropy :=
  entropy_gap_ge_octic_defect (by decide) a ha _ _ _ _ _ W4_exp_integrable (W4_moment_comparison a ha)

theorem entropy_gap_five (a : Fin 5 → ℝ) (ha : IsUnit a) :
    (1 / 100 : ℝ) * deficit a - sigma5 ≤
      (Spline.diagonalFiniteEntropyDensity 5 (by decide)).entropy -
        (projectionFiniteEntropyDensity a ha).entropy :=
  entropy_gap_ge_octic_defect (by decide) a ha _ _ _ _ _ W5_exp_integrable (W5_moment_comparison a ha)

theorem entropy_gap_six (a : Fin 6 → ℝ) (ha : IsUnit a) :
    (19 / 2000 : ℝ) * deficit a - sigma6 ≤
      (Spline.diagonalFiniteEntropyDensity 6 (by decide)).entropy -
        (projectionFiniteEntropyDensity a ha).entropy :=
  entropy_gap_ge_octic_defect (by decide) a ha _ _ _ _ _ W6_exp_integrable (W6_moment_comparison a ha)

theorem exterior_three_of_sigma_bound (hsigma : sigma3 ≤ 9 / 100000)
    (a : Fin 3 → ℝ) (ha : IsUnit a) (hdelta : 1 / 100 ≤ deficit a) :
    deficit a / 1000 ≤ (Spline.diagonalFiniteEntropyDensity 3 (by decide)).entropy -
      (projectionFiniteEntropyDensity a ha).entropy := by
  have h := entropy_gap_three a ha
  linarith

theorem exterior_four_of_sigma_bound (hsigma : sigma4 ≤ 1 / 50000)
    (a : Fin 4 → ℝ) (ha : IsUnit a) (hdelta : 1 / 500 ≤ deficit a) :
    deficit a / 1000 ≤ (Spline.diagonalFiniteEntropyDensity 4 (by decide)).entropy -
      (projectionFiniteEntropyDensity a ha).entropy := by
  have h := entropy_gap_four a ha
  linarith

theorem exterior_five_of_sigma_bound (hsigma : sigma5 ≤ 1 / 200000)
    (a : Fin 5 → ℝ) (ha : IsUnit a) (hdelta : 7 / 12500 ≤ deficit a) :
    deficit a / 1000 ≤ (Spline.diagonalFiniteEntropyDensity 5 (by decide)).entropy -
      (projectionFiniteEntropyDensity a ha).entropy := by
  have h := entropy_gap_five a ha
  linarith

theorem exterior_six_of_sigma_bound (hsigma : sigma6 ≤ 7 / 5000000)
    (a : Fin 6 → ℝ) (ha : IsUnit a) (hdelta : 1 / 6000 ≤ deficit a) :
    deficit a / 1000 ≤ (Spline.diagonalFiniteEntropyDensity 6 (by decide)).entropy -
      (projectionFiniteEntropyDensity a ha).entropy := by
  have h := entropy_gap_six a ha
  linarith

end
end ENT.Small
