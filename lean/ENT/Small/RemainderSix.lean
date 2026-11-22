module

public import ENT.Small.PureRemainderSoundness
public import ENT.Small.PureRemainderData.M6Certified

/-! Actual dimension-6 remainder bound from exact pure rational witnesses. -/

@[expose] public section
set_option autoImplicit false
namespace ENT.Small
noncomputable section
open PureRemainder PureRemainder.Certified

theorem logThirdEnvelope_six_bound :
    ∃ H : LogThirdEnvelope 6 (1 / 25 : ℝ),
      averagedRemainderBound 6 H.bound ≤ (13 / 2 : ℝ) := by
  have h := remainderBound_from_pure_grid 6 (by decide) 160
    M6DerivativeGrid M6DerivativeGrid_valid rfl
    (1 / 25) (by norm_num) 10 (by norm_num)
    (fun v hv => logThirdUnitSum_six_outer hv)
    M6Step M6Area M6Step_valid M6Area_valid M6Geometry
    (by norm_num) (13 / 2) (by simpa only [show Nat.factorial 5 = 120 from rfl, Nat.cast_ofNat] using M6Numeric.le)
  have hγ : ((1 / 25 : ℚ) : ℝ) = (1 / 25 : ℝ) := by norm_num
  have hU : ((13 / 2 : ℚ) : ℝ) = (13 / 2 : ℝ) := by norm_num
  rw [hγ, hU] at h
  exact h

end
end ENT.Small
