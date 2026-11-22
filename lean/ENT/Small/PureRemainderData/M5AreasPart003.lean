module

public import ENT.Small.PureRemainderData.M5Data

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace ENT.Small.PureRemainder.Certified

def M5AreasPart3 := (M5Areas).drop 96 |>.take 32

theorem M5AreasPart3_valid :
    M5AreasPart3.all (fun c => decide c.Valid) = true := by decide +kernel

end ENT.Small.PureRemainder.Certified
