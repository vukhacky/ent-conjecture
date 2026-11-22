module

public import ENT.Small.PureRemainderData.M5All
public import Mathlib.Data.Fintype.Fin

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace ENT.Small.PureRemainder.Certified

theorem M5Steps_length : M5Steps.length = 128 := by decide +kernel

theorem M5Areas_length : M5Areas.length = 128 := by decide +kernel

def M5Step (i : Fin 128) : ExpandedStep :=
  M5Steps.get ⟨i, by simpa only [M5Steps_length] using i.isLt⟩

def M5Area (i : Fin 128) : CubeAreaCertificate :=
  M5Areas.get ⟨i, by simpa only [M5Areas_length] using i.isLt⟩

theorem M5Step_valid (i : Fin 128) : (M5Step i).Valid M5DerivativeGrid :=
  get_valid_of_all M5Steps M5Steps_all _

theorem M5Area_valid (i : Fin 128) : (M5Area i).Valid :=
  get_valid_of_all M5Areas M5Areas_all _

theorem M5Geometry : ∀ i : Fin 128,
  (M5Step i).a = (1/2:ℚ) + (i:ℚ)/64 ∧
  (M5Step i).b = (1/2:ℚ) + ((i:ℚ)+1)/64 ∧
  (M5Step i).gamma = (29 / 500 : ℚ) ∧
  (M5Area i).n = 5 ∧
  ((M5Area i).k:ℚ)+(M5Area i).a = (M5Step i).a ∧
  ((M5Area i).k:ℚ)+(M5Area i).b = (M5Step i).b := by decide +kernel

theorem M5Numeric :
  2 * (8/(1-(29 / 500 : ℚ))^3) * (1/(5*24*2^5):ℚ) +
    2 * (∑ i : Fin 128, (M5Step i).bound*(M5Area i).area) < (77 / 10 : ℚ) := by decide +kernel

end ENT.Small.PureRemainder.Certified
