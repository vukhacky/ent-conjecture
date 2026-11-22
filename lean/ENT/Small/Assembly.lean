module

public import ENT.Basic.ProjectionDensity
public import ENT.Basic.Symmetry

/-! Entropy-gap assembly with all premises explicit. Concrete dimension
theorems must discharge the gap hypothesis before being declared closed. -/

@[expose] public section
set_option autoImplicit false

namespace ENT
noncomputable section

theorem entAt_of_positive_deficit_gap {n : ℕ}
    (q : FiniteEntropyDensity (projectionLaw (diagonal n))) {c : ℝ} (hc : 0<c)
    (hgap : ∀ (a : Fin n → ℝ) (ha : IsUnit a),
      c*deficit a≤q.entropy-(projectionFiniteEntropyDensity a ha).entropy) : ENTAt n := by
  intro a ha
  let p := projectionFiniteEntropyDensity a ha
  have hδ := deficit_nonneg a
  have h := hgap a ha
  refine ⟨p,q,by nlinarith,?_⟩
  constructor
  · intro heq
    apply (deficit_eq_zero_iff a).mp
    change p.entropy=q.entropy at heq
    change c*deficit a≤q.entropy-p.entropy at h
    nlinarith
  · intro hdiag
    have hlaw := projectionLaw_eq_diagonal_of_isDiagonal a hdiag
    have heq := p.entropy_eq (q.transport hlaw.symm)
    simpa only [FiniteEntropyDensity.entropy_transport] using heq

end
end ENT
