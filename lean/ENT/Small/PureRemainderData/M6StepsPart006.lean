module

public import ENT.Small.PureRemainderData.M6Data

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace ENT.Small.PureRemainder.Certified

def M6StepsPart6 := (M6Steps).drop 48 |>.take 8

theorem M6StepsPart6_valid :
    M6StepsPart6.all (fun c => decide (c.Valid M6DerivativeGrid)) = true := by decide +kernel

end ENT.Small.PureRemainder.Certified
