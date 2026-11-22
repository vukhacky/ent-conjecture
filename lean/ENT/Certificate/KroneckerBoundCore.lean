module

public import ENT.Certificate.Pure

/-! Executable natural bounds used by exact evaluation certificates.
Their polynomial meaning is proved in KroneckerBounds. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Certificate.Kronecker

def sumAbs (p : List ℤ) : ℕ := (p.map Int.natAbs).sum

def tripleFactor (d : ℕ) : ℕ := (3 * d + 1) * (2 * d + 1)

def curvatureCoeffBound (n k d M : ℕ) : ℕ :=
  tripleFactor d * M ^ 3 * (6 * n ^ 3 * d ^ 3 + 56 * (n + 2 * k) + 112)

def bernsteinCoeffBound (D : ℕ) (bs : List ℤ) : ℕ := sumAbs bs * 2 ^ D

end ENT.Certificate.Kronecker
