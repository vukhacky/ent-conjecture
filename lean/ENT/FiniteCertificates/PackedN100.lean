module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerDirectData.N100Part03
public import ENT.Pilot.KroneckerDirectData.N100Part04
public import ENT.Pilot.KroneckerDirectData.N100Part05
public import ENT.Pilot.KroneckerDirectData.N100Part06
public import ENT.Pilot.KroneckerSplineData.N100Part00
public import ENT.Pilot.KroneckerSplineData.N100Part01
public import ENT.Pilot.KroneckerSplineData.N100Part02
public import ENT.Certificate.KroneckerSplineSoundness
public import ENT.Certificate.KroneckerDirectSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_100 : PackedFamily 100 := by
  intro k hk0 hk2
  have hkmax : k ≤ 49 := by omega
  interval_cases k
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k1_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k2_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k3_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k4_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k5_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k6_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k7_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k8_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k9_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k10_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k11_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k12_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k13_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k14_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k15_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k16_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k17_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k18_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k19_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k20_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k21_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k22_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k23_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n100k24_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k25_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k26_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k27_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k28_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k29_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k30_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k31_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k32_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k33_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k34_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k35_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k36_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k37_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k38_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k39_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k40_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k41_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k42_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k43_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k44_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k45_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k46_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k47_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k48_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n100k49_exists

end ENT.FiniteCertificates
