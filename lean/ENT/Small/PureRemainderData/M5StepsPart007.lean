module

public import ENT.Small.PureRemainderData.M5Data

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace ENT.Small.PureRemainder.Certified

def M5StepsPart7 := (M5Steps).drop 56 |>.take 8

theorem M5StepsPart7_valid :
    M5StepsPart7.all (fun c => decide (c.Valid M5DerivativeGrid)) = true := by decide +kernel

end ENT.Small.PureRemainder.Certified
