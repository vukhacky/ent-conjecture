module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerSplineData.N090Part00
public import ENT.Pilot.KroneckerSplineData.N090Part01
public import ENT.Pilot.KroneckerSplineData.N090Part02
public import ENT.Pilot.KroneckerSplineData.N090Part03
public import ENT.Pilot.KroneckerSplineData.N090Part04
public import ENT.Pilot.KroneckerSplineData.N090Part05
public import ENT.Certificate.KroneckerSplineSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_90 : PackedFamily 90 := by
  intro k hk0 hk2
  have hkmax : k ≤ 44 := by omega
  interval_cases k
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k1_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k2_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k3_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k4_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k5_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k6_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k7_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k8_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k9_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k10_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k11_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k12_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k13_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k14_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k15_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k16_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k17_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k18_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k19_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k20_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k21_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k22_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k23_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k24_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k25_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k26_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k27_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k28_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k29_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k30_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k31_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k32_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k33_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k34_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k35_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k36_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k37_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k38_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k39_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k40_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k41_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k42_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k43_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n90k44_exists

end ENT.FiniteCertificates
