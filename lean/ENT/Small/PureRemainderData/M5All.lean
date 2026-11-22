module

public import ENT.Small.PureRemainderData.M5Pilot32
public import ENT.Small.PureRemainderData.M5GridPart001
public import ENT.Small.PureRemainderData.M5GridPart002
public import ENT.Small.PureRemainderData.M5GridPart003
public import ENT.Small.PureRemainderData.M5GridPart004
public import ENT.Small.PureRemainderData.M5GridPart005
public import ENT.Small.PureRemainderData.M5GridPart006
public import ENT.Small.PureRemainderData.M5GridPart007
public import ENT.Small.PureRemainderData.M5GridPart008
public import ENT.Small.PureRemainderData.M5GridPart009
public import ENT.Small.PureRemainderData.M5GridPart010
public import ENT.Small.PureRemainderData.M5GridPart011
public import ENT.Small.PureRemainderData.M5GridPart012
public import ENT.Small.PureRemainderData.M5GridPart013
public import ENT.Small.PureRemainderData.M5GridPart014
public import ENT.Small.PureRemainderData.M5GridPart015
public import ENT.Small.PureRemainderData.M5GridPart016
public import ENT.Small.PureRemainderData.M5StepsPart000
public import ENT.Small.PureRemainderData.M5StepsPart001
public import ENT.Small.PureRemainderData.M5StepsPart002
public import ENT.Small.PureRemainderData.M5StepsPart003
public import ENT.Small.PureRemainderData.M5StepsPart004
public import ENT.Small.PureRemainderData.M5StepsPart005
public import ENT.Small.PureRemainderData.M5StepsPart006
public import ENT.Small.PureRemainderData.M5StepsPart007
public import ENT.Small.PureRemainderData.M5StepsPart008
public import ENT.Small.PureRemainderData.M5StepsPart009
public import ENT.Small.PureRemainderData.M5StepsPart010
public import ENT.Small.PureRemainderData.M5StepsPart011
public import ENT.Small.PureRemainderData.M5StepsPart012
public import ENT.Small.PureRemainderData.M5StepsPart013
public import ENT.Small.PureRemainderData.M5StepsPart014
public import ENT.Small.PureRemainderData.M5StepsPart015
public import ENT.Small.PureRemainderData.M5AreasPart000
public import ENT.Small.PureRemainderData.M5AreasPart001
public import ENT.Small.PureRemainderData.M5AreasPart002
public import ENT.Small.PureRemainderData.M5AreasPart003

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace ENT.Small.PureRemainder.Certified

theorem M5Grid_split : M5DerivativeGrid.boxes.zipIdx = M5GridPart0 ++ M5GridPart1 ++ M5GridPart2 ++ M5GridPart3 ++ M5GridPart4 ++ M5GridPart5 ++ M5GridPart6 ++ M5GridPart7 ++ M5GridPart8 ++ M5GridPart9 ++ M5GridPart10 ++ M5GridPart11 ++ M5GridPart12 ++ M5GridPart13 ++ M5GridPart14 ++ M5GridPart15 ++ M5GridPart16 := by rfl

theorem M5Grid_all : (M5DerivativeGrid.boxes.zipIdx).all (fun bi => decide (gridCondition M5DerivativeGrid bi)) = true := by
  rw [M5Grid_split]
  simp only [List.all_append, M5GridPart0_valid, M5GridPart1_valid, M5GridPart2_valid, M5GridPart3_valid, M5GridPart4_valid, M5GridPart5_valid, M5GridPart6_valid, M5GridPart7_valid, M5GridPart8_valid, M5GridPart9_valid, M5GridPart10_valid, M5GridPart11_valid, M5GridPart12_valid, M5GridPart13_valid, M5GridPart14_valid, M5GridPart15_valid, M5GridPart16_valid, Bool.true_and]

theorem M5Steps_split : M5Steps = M5StepsPart0 ++ M5StepsPart1 ++ M5StepsPart2 ++ M5StepsPart3 ++ M5StepsPart4 ++ M5StepsPart5 ++ M5StepsPart6 ++ M5StepsPart7 ++ M5StepsPart8 ++ M5StepsPart9 ++ M5StepsPart10 ++ M5StepsPart11 ++ M5StepsPart12 ++ M5StepsPart13 ++ M5StepsPart14 ++ M5StepsPart15 := by rfl

theorem M5Steps_all : (M5Steps).all (fun c => decide (c.Valid M5DerivativeGrid)) = true := by
  rw [M5Steps_split]
  simp only [List.all_append, M5StepsPart0_valid, M5StepsPart1_valid, M5StepsPart2_valid, M5StepsPart3_valid, M5StepsPart4_valid, M5StepsPart5_valid, M5StepsPart6_valid, M5StepsPart7_valid, M5StepsPart8_valid, M5StepsPart9_valid, M5StepsPart10_valid, M5StepsPart11_valid, M5StepsPart12_valid, M5StepsPart13_valid, M5StepsPart14_valid, M5StepsPart15_valid, Bool.true_and]

theorem M5Areas_split : M5Areas = M5AreasPart0 ++ M5AreasPart1 ++ M5AreasPart2 ++ M5AreasPart3 := by rfl

theorem M5Areas_all : (M5Areas).all (fun c => decide c.Valid) = true := by
  rw [M5Areas_split]
  simp only [List.all_append, M5AreasPart0_valid, M5AreasPart1_valid, M5AreasPart2_valid, M5AreasPart3_valid, Bool.true_and]

theorem M5DerivativeGrid_valid : M5DerivativeGrid.Valid :=
  gridValid_of_all M5DerivativeGrid (by decide +kernel) M5Grid_all

end ENT.Small.PureRemainder.Certified
