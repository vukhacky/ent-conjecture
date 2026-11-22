module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerDirectData.N110Part00
public import ENT.Pilot.KroneckerDirectData.N110Part01
public import ENT.Pilot.KroneckerDirectData.N110Part02
public import ENT.Pilot.KroneckerDirectData.N110Part03
public import ENT.Pilot.KroneckerDirectData.N110Part04
public import ENT.Pilot.KroneckerDirectData.N110Part05
public import ENT.Pilot.KroneckerDirectData.N110Part06
public import ENT.Certificate.KroneckerDirectSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_110 : PackedFamily 110 := by
  intro k hk0 hk2
  have hkmax : k ≤ 54 := by omega
  interval_cases k
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k1_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k2_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k3_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k4_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k5_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k6_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k7_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k8_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k9_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k10_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k11_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k12_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k13_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k14_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k15_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k16_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k17_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k18_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k19_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k20_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k21_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k22_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k23_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k24_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k25_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k26_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k27_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k28_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k29_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k30_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k31_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k32_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k33_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k34_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k35_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k36_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k37_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k38_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k39_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k40_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k41_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k42_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k43_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k44_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k45_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k46_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k47_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k48_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k49_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k50_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k51_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k52_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k53_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n110k54_exists

end ENT.FiniteCertificates
