module

public import ENT.Small.PureRemainderData.M6Data

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace ENT.Small.PureRemainder.Certified

def M6AreasPart1 := (M6Areas).drop 32 |>.take 32

theorem M6AreasPart1_valid :
    M6AreasPart1.all (fun c => decide c.Valid) = true := by decide +kernel

end ENT.Small.PureRemainder.Certified
