module

public import ENT.Small.PureRemainderSoundness
public import ENT.Small.PureRemainderData.M5Certified

/-! Actual dimension-5 remainder bound from exact pure rational witnesses. -/

@[expose] public section
set_option autoImplicit false
namespace ENT.Small
noncomputable section
open PureRemainder PureRemainder.Certified

theorem logThirdEnvelope_five_bound :
    ∃ H : LogThirdEnvelope 5 (29 / 500 : ℝ),
      averagedRemainderBound 5 H.bound ≤ (77 / 10 : ℝ) := by
  have h := remainderBound_from_pure_grid 5 (by decide) 128
    M5DerivativeGrid M5DerivativeGrid_valid rfl
    (29 / 500) (by norm_num) 8 (by norm_num)
    (fun v hv => logThirdUnitSum_five_outer hv)
    M5Step M5Area M5Step_valid M5Area_valid M5Geometry
    (by norm_num) (77 / 10) (by simpa only [show Nat.factorial 4 = 24 from rfl, Nat.cast_ofNat] using M5Numeric.le)
  have hγ : ((29 / 500 : ℚ) : ℝ) = (29 / 500 : ℝ) := by norm_num
  have hU : ((77 / 10 : ℚ) : ℝ) = (77 / 10 : ℝ) := by norm_num
  rw [hγ, hU] at h
  exact h

end
end ENT.Small
