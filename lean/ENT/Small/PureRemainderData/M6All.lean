module

public import ENT.Small.PureRemainderData.M6GridPart000
public import ENT.Small.PureRemainderData.M6GridPart001
public import ENT.Small.PureRemainderData.M6GridPart002
public import ENT.Small.PureRemainderData.M6GridPart003
public import ENT.Small.PureRemainderData.M6GridPart004
public import ENT.Small.PureRemainderData.M6GridPart005
public import ENT.Small.PureRemainderData.M6GridPart006
public import ENT.Small.PureRemainderData.M6GridPart007
public import ENT.Small.PureRemainderData.M6GridPart008
public import ENT.Small.PureRemainderData.M6GridPart009
public import ENT.Small.PureRemainderData.M6GridPart010
public import ENT.Small.PureRemainderData.M6GridPart011
public import ENT.Small.PureRemainderData.M6GridPart012
public import ENT.Small.PureRemainderData.M6GridPart013
public import ENT.Small.PureRemainderData.M6GridPart014
public import ENT.Small.PureRemainderData.M6GridPart015
public import ENT.Small.PureRemainderData.M6GridPart016
public import ENT.Small.PureRemainderData.M6GridPart017
public import ENT.Small.PureRemainderData.M6GridPart018
public import ENT.Small.PureRemainderData.M6GridPart019
public import ENT.Small.PureRemainderData.M6GridPart020
public import ENT.Small.PureRemainderData.M6StepsPart000
public import ENT.Small.PureRemainderData.M6StepsPart001
public import ENT.Small.PureRemainderData.M6StepsPart002
public import ENT.Small.PureRemainderData.M6StepsPart003
public import ENT.Small.PureRemainderData.M6StepsPart004
public import ENT.Small.PureRemainderData.M6StepsPart005
public import ENT.Small.PureRemainderData.M6StepsPart006
public import ENT.Small.PureRemainderData.M6StepsPart007
public import ENT.Small.PureRemainderData.M6StepsPart008
public import ENT.Small.PureRemainderData.M6StepsPart009
public import ENT.Small.PureRemainderData.M6StepsPart010
public import ENT.Small.PureRemainderData.M6StepsPart011
public import ENT.Small.PureRemainderData.M6StepsPart012
public import ENT.Small.PureRemainderData.M6StepsPart013
public import ENT.Small.PureRemainderData.M6StepsPart014
public import ENT.Small.PureRemainderData.M6StepsPart015
public import ENT.Small.PureRemainderData.M6StepsPart016
public import ENT.Small.PureRemainderData.M6StepsPart017
public import ENT.Small.PureRemainderData.M6StepsPart018
public import ENT.Small.PureRemainderData.M6StepsPart019
public import ENT.Small.PureRemainderData.M6AreasPart000
public import ENT.Small.PureRemainderData.M6AreasPart001
public import ENT.Small.PureRemainderData.M6AreasPart002
public import ENT.Small.PureRemainderData.M6AreasPart003
public import ENT.Small.PureRemainderData.M6AreasPart004

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace ENT.Small.PureRemainder.Certified

theorem M6Grid_split : M6DerivativeGrid.boxes.zipIdx = M6GridPart0 ++ M6GridPart1 ++ M6GridPart2 ++ M6GridPart3 ++ M6GridPart4 ++ M6GridPart5 ++ M6GridPart6 ++ M6GridPart7 ++ M6GridPart8 ++ M6GridPart9 ++ M6GridPart10 ++ M6GridPart11 ++ M6GridPart12 ++ M6GridPart13 ++ M6GridPart14 ++ M6GridPart15 ++ M6GridPart16 ++ M6GridPart17 ++ M6GridPart18 ++ M6GridPart19 ++ M6GridPart20 := by rfl

theorem M6Grid_all : (M6DerivativeGrid.boxes.zipIdx).all (fun bi => decide (gridCondition M6DerivativeGrid bi)) = true := by
  rw [M6Grid_split]
  simp only [List.all_append, M6GridPart0_valid, M6GridPart1_valid, M6GridPart2_valid, M6GridPart3_valid, M6GridPart4_valid, M6GridPart5_valid, M6GridPart6_valid, M6GridPart7_valid, M6GridPart8_valid, M6GridPart9_valid, M6GridPart10_valid, M6GridPart11_valid, M6GridPart12_valid, M6GridPart13_valid, M6GridPart14_valid, M6GridPart15_valid, M6GridPart16_valid, M6GridPart17_valid, M6GridPart18_valid, M6GridPart19_valid, M6GridPart20_valid, Bool.true_and]

theorem M6Steps_split : M6Steps = M6StepsPart0 ++ M6StepsPart1 ++ M6StepsPart2 ++ M6StepsPart3 ++ M6StepsPart4 ++ M6StepsPart5 ++ M6StepsPart6 ++ M6StepsPart7 ++ M6StepsPart8 ++ M6StepsPart9 ++ M6StepsPart10 ++ M6StepsPart11 ++ M6StepsPart12 ++ M6StepsPart13 ++ M6StepsPart14 ++ M6StepsPart15 ++ M6StepsPart16 ++ M6StepsPart17 ++ M6StepsPart18 ++ M6StepsPart19 := by rfl

theorem M6Steps_all : (M6Steps).all (fun c => decide (c.Valid M6DerivativeGrid)) = true := by
  rw [M6Steps_split]
  simp only [List.all_append, M6StepsPart0_valid, M6StepsPart1_valid, M6StepsPart2_valid, M6StepsPart3_valid, M6StepsPart4_valid, M6StepsPart5_valid, M6StepsPart6_valid, M6StepsPart7_valid, M6StepsPart8_valid, M6StepsPart9_valid, M6StepsPart10_valid, M6StepsPart11_valid, M6StepsPart12_valid, M6StepsPart13_valid, M6StepsPart14_valid, M6StepsPart15_valid, M6StepsPart16_valid, M6StepsPart17_valid, M6StepsPart18_valid, M6StepsPart19_valid, Bool.true_and]

theorem M6Areas_split : M6Areas = M6AreasPart0 ++ M6AreasPart1 ++ M6AreasPart2 ++ M6AreasPart3 ++ M6AreasPart4 := by rfl

theorem M6Areas_all : (M6Areas).all (fun c => decide c.Valid) = true := by
  rw [M6Areas_split]
  simp only [List.all_append, M6AreasPart0_valid, M6AreasPart1_valid, M6AreasPart2_valid, M6AreasPart3_valid, M6AreasPart4_valid, Bool.true_and]

theorem M6DerivativeGrid_valid : M6DerivativeGrid.Valid :=
  gridValid_of_all M6DerivativeGrid (by decide +kernel) M6Grid_all

end ENT.Small.PureRemainder.Certified
