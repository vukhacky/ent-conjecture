module

public import ENT.Certificate.BlockCore

/-! Coefficient-wise canonical spline checks.  The binomial coefficient common
to the truncated-power sum is factored out before kernel evaluation.  This
module contains only executable definitions; BlockSplineCoefficients proves
their exact connection with PureFast.fastSplineCoeffs. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Certificate.Block

def directSplineCoeff (n k i : ℕ) : ℤ :=
  (Nat.fast_choose (n - 1) i : ℤ) *
    ((List.range (k + 1)).map (fun j =>
      (-1 : ℤ) ^ j * (Nat.fast_choose n j : ℤ) *
        ((k : ℤ) - (j : ℤ)) ^ (n - 1 - i))).sum

end ENT.Certificate.Block
