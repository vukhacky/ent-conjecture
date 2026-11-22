module

public import ENT.Comparison.KLInterior
public import ENT.Basic.ProjectionDensity
public import ENT.Basic.ProjectionMoments

/-! Deduce the entropy comparison from the expectation comparison for the diagonal potential. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory

namespace ENT
noncomputable section

theorem entAt_of_diagonal_potential_comparison {n : ℕ} (hn : 2 ≤ n)
    (hcomparison : ∀ (a : Fin n → ℝ), IsUnit a →
      (∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw a) ≤
        ∫ x, Spline.diagonalSplinePotential n x ∂projectionLaw (diagonal n)) :
    ENTAt n := by
  intro a ha
  let p := projectionFiniteEntropyDensity a ha
  let q := Spline.diagonalFiniteEntropyDensity n hn
  refine ⟨p, q, ?_⟩
  by_cases hdiag : IsDiagonal a
  · have hlaw := projectionLaw_eq_diagonal_of_isDiagonal a hdiag
    have heq : p.entropy = q.entropy := by
      have h := p.entropy_eq (q.transport hlaw.symm)
      simpa only [FiniteEntropyDensity.entropy_transport] using h
    exact ⟨heq.le, ⟨fun _ => hdiag, fun _ => heq⟩⟩
  · have hkl : FiniteKLData p q := diagonalFiniteKLData hn a ha hdiag p
    have hgap : 0 ≤ ∫ x, (p.density x - q.density x) * Real.log (q.density x) := by
      rw [hkl.potential_gap_eq_law_integrals]
      exact sub_nonneg.mpr (hcomparison a ha)
    exact ⟨hkl.entropy_le hgap,
      (hkl.entropy_eq_iff hgap).trans
        (projectionLaw_eq_diagonal_iff_isDiagonal (by omega) a ha)⟩

end
end ENT
