module

public import ENT.Small.PureRemainderData.M5Data

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace ENT.Small.PureRemainder.Certified

def M5GridPart5 := (M5DerivativeGrid.boxes.zipIdx).drop 160 |>.take 32

theorem M5GridPart5_valid :
    M5GridPart5.all (fun bi => decide (gridCondition M5DerivativeGrid bi)) = true := by decide +kernel

end ENT.Small.PureRemainder.Certified
