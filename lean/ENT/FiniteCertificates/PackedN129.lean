module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerDirectData.N129Part00
public import ENT.Pilot.KroneckerDirectData.N129Part01
public import ENT.Pilot.KroneckerDirectData.N129Part02
public import ENT.Pilot.KroneckerDirectData.N129Part03
public import ENT.Pilot.KroneckerDirectData.N129Part04
public import ENT.Pilot.KroneckerDirectData.N129Part05
public import ENT.Pilot.KroneckerDirectData.N129Part06
public import ENT.Pilot.KroneckerDirectData.N129Part07
public import ENT.Certificate.KroneckerDirectSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_129 : PackedFamily 129 := by
  intro k hk0 hk2
  have hkmax : k ≤ 64 := by omega
  interval_cases k
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k1_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k2_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k3_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k4_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k5_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k6_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k7_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k8_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k9_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k10_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k11_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k12_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k13_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k14_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k15_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k16_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k17_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k18_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k19_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k20_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k21_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k22_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k23_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k24_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k25_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k26_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k27_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k28_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k29_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k30_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k31_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k32_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k33_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k34_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k35_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k36_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k37_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k38_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k39_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k40_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k41_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k42_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k43_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k44_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k45_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k46_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k47_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k48_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k49_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k50_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k51_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k52_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k53_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k54_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k55_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k56_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k57_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k58_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k59_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k60_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k61_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k62_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k63_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n129k64_exists

end ENT.FiniteCertificates
