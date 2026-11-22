module

public import ENT.Small.EnclosuresEntropyFour
public import ENT.Small.QuadratureJ4
public import ENT.Small.FourLocal

/-! The nine actual scalar bounds used by the local four-dimensional proof. -/

@[expose] public section
set_option autoImplicit false
namespace ENT.Small
noncomputable section

theorem fourV_bounds : (179175946921/100000000000:ℝ) ≤ fourV ∧
    fourV ≤ (179175946925/100000000000:ℝ) := by
  rw [fourV,log_six_eq]
  constructor <;> linarith [log_two_bounds.1,log_two_bounds.2,log_three_bounds.1,log_three_bounds.2]

theorem fourLocalScalarBounds : FourLocalScalarBounds := by
  have hh := fourH_bounds
  have hv := fourV_bounds
  have hj2 := fourJ2_bounds
  have hj3 := fourJ3_bounds
  constructor
  · unfold fourAlpha; linarith [hh.1,hh.2,hj2.1,hj2.2]
  · unfold fourC fourF2R; linarith [hh.1,hh.2,hv.1,hv.2,hj3.1,hj3.2]
  · unfold fourE; linarith [hh.1,hj3.2]
  · unfold fourE; linarith [hh.2,hj3.1]
  · unfold fourK; linarith [hh.2,hj3.2]
  · linarith [hh.1]
  · linarith [hv.1,hh.2]
  · linarith [hv.2,hh.1]
  · linarith [hv.1,hh.2]

end
end ENT.Small
