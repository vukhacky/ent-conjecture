module

public import ENT.Pilot.N7
public import ENT.Certificate.CompleteChecker

/-! All four n=7 cells accepted by the complete semantic checker. -/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open ENT.Certificate

namespace ENT.Pilot

theorem n7k0_complete_check : checkCell n7k0Data = true := by decide +kernel
theorem n7k1_complete_check : checkCell n7k1Data = true := by decide +kernel
theorem n7k2_complete_check : checkCell n7k2Data = true := by decide +kernel
theorem n7k3_complete_check : checkCell n7k3Data = true := by decide +kernel

theorem dimension7_complete_cell_conclusions :
    CellConclusion n7k0Data ∧ CellConclusion n7k1Data ∧
      CellConclusion n7k2Data ∧ CellConclusion n7k3Data :=
  ⟨checkCell_sound _ n7k0_complete_check, checkCell_sound _ n7k1_complete_check,
    checkCell_sound _ n7k2_complete_check, checkCell_sound _ n7k3_complete_check⟩

end ENT.Pilot
