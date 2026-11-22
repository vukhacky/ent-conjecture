module

public import ENT.Certificate.Family
public import ENT.Certificate.KroneckerCore

/-! Families of cell certificates for finite dimension ranges. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

def PackedValid (c : Certificate.Pure.CellData) : Prop :=
  ∃ rBase bBase : ℤ, Certificate.Kronecker.Valid c rBase bBase

abbrev PackedFamily (n : ℕ) : Prop := Spline.PurePropCellFamily PackedValid n

end ENT.FiniteCertificates
