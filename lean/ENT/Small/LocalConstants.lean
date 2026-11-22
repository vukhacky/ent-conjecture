module

public import ENT.Spline.DensityLaw
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Actual integrals and a measurable envelope interface for the local n=5,6
argument. The enclosure is permitted to exceed the moving supremum; its
pointwise domination and weighted integrability must be proved. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Small
noncomputable section

def smallKappa (n : ℕ) : ℝ :=
  1 - (n : ℝ) * ∫ t in (0 : ℝ)..(n : ℝ),
    (Spline.unitSumSplineDensity (n - 2) (t - 1) - Spline.unitSumSplineDensity n t) *
      Real.log (Spline.unitSumSplineDensity n t)

def logThirdUnitSum (n : ℕ) (x : ℝ) : ℝ :=
  deriv (deriv (deriv (fun t => Real.log (Spline.unitSumSplineDensity n t)))) x

def averagedRemainderBound (n : ℕ) (H : ℝ → ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..((n : ℝ) / 2), Spline.unitSumSplineDensity n t * t ^ 3 * H t

structure LogThirdEnvelope (n : ℕ) (γ : ℝ) where
  bound : ℝ → ℝ
  measurable : Measurable bound
  nonneg : ∀ t, 0 ≤ bound t
  dominates : ∀ t ∈ Ioc (0 : ℝ) ((n : ℝ) / 2),
    ∀ v ∈ Icc ((1 - γ) * t) (min ((n : ℝ) / 2) ((1 + γ) * t)),
      |logThirdUnitSum n v| ≤ bound t
  weighted_integrable : IntervalIntegrable
    (fun t => Spline.unitSumSplineDensity n t * t ^ 3 * bound t) volume 0 ((n : ℝ) / 2)

theorem averagedRemainderBound_nonneg {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (H : LogThirdEnvelope n γ) : 0 ≤ averagedRemainderBound n H.bound := by
  unfold averagedRemainderBound
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
  intro t ht
  exact mul_nonneg (mul_nonneg (Spline.unitSumSplineDensity_nonneg n hn t)
    (pow_nonneg ht.1 3)) (H.nonneg t)

end
end ENT.Small
