module

public import ENT.Certificate.Pure

/-! Certificate coverage of the reflected spline cells. The corresponding polynomial inequalities are proved in `ENT.Spline.PureCertificateBridge`. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Spline

open ENT.Certificate

/-- The original Boolean acceptance family, with its exact body preserved. -/
def PureCellFamily (check : Pure.CellData → Bool) (n : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → 2 * k < n →
    ∃ c : Pure.CellData, c.n = n ∧ c.k = k ∧ check c = true

/-- Coverage by a proved cell predicate, allowing separately checked auxiliary
arithmetic witnesses without recomputing a monolithic Boolean checker. -/
def PurePropCellFamily (valid : Pure.CellData → Prop) (n : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → 2 * k < n →
    ∃ c : Pure.CellData, c.n = n ∧ c.k = k ∧ valid c

end ENT.Spline
