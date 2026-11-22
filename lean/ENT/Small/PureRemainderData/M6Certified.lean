module

public import ENT.Small.PureRemainderData.M6All
public import Mathlib.Data.Fintype.Fin

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace ENT.Small.PureRemainder.Certified

theorem M6Steps_length : M6Steps.length = 160 := by decide +kernel

theorem M6Areas_length : M6Areas.length = 160 := by decide +kernel

def M6Step (i : Fin 160) : ExpandedStep :=
  M6Steps.get ⟨i, by simpa only [M6Steps_length] using i.isLt⟩

def M6Area (i : Fin 160) : CubeAreaCertificate :=
  M6Areas.get ⟨i, by simpa only [M6Areas_length] using i.isLt⟩

theorem M6Step_valid (i : Fin 160) : (M6Step i).Valid M6DerivativeGrid :=
  get_valid_of_all M6Steps M6Steps_all _

theorem M6Area_valid (i : Fin 160) : (M6Area i).Valid :=
  get_valid_of_all M6Areas M6Areas_all _

theorem M6Geometry : ∀ i : Fin 160,
  (M6Step i).a = (1/2:ℚ) + (i:ℚ)/64 ∧
  (M6Step i).b = (1/2:ℚ) + ((i:ℚ)+1)/64 ∧
  (M6Step i).gamma = (1 / 25 : ℚ) ∧
  (M6Area i).n = 6 ∧
  ((M6Area i).k:ℚ)+(M6Area i).a = (M6Step i).a ∧
  ((M6Area i).k:ℚ)+(M6Area i).b = (M6Step i).b := by decide +kernel

theorem M6Numeric :
  2 * (10/(1-(1 / 25 : ℚ))^3) * (1/(6*120*2^6):ℚ) +
    2 * (∑ i : Fin 160, (M6Step i).bound*(M6Area i).area) < (13 / 2 : ℚ) := by decide +kernel

end ENT.Small.PureRemainder.Certified
