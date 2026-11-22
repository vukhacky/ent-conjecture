module

public import ENT.Small.PureRemainderData.M5Data

/-! Grid-condition proof for the first 32 dimension-five boxes. -/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ENT.Small.PureRemainder.Certified

def M5GridPart0 := (M5DerivativeGrid.boxes.zipIdx).drop 0 |>.take 32

theorem M5GridPart0_valid :
    M5GridPart0.all (fun bi => decide (gridCondition M5DerivativeGrid bi)) = true := by
  decide +kernel

end ENT.Small.PureRemainder.Certified
