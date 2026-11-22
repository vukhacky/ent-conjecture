module

public import ENT.Small.PureRemainderData.M6Data

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace ENT.Small.PureRemainder.Certified

def M6GridPart19 := (M6DerivativeGrid.boxes.zipIdx).drop 608 |>.take 32

theorem M6GridPart19_valid :
    M6GridPart19.all (fun bi => decide (gridCondition M6DerivativeGrid bi)) = true := by decide +kernel

end ENT.Small.PureRemainder.Certified
