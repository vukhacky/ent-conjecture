module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerDirectData.N143Part00
public import ENT.Pilot.KroneckerDirectData.N143Part01
public import ENT.Pilot.KroneckerDirectData.N143Part02
public import ENT.Pilot.KroneckerDirectData.N143Part03
public import ENT.Pilot.KroneckerDirectData.N143Part04
public import ENT.Pilot.KroneckerDirectData.N143Part05
public import ENT.Pilot.KroneckerDirectData.N143Part06
public import ENT.Pilot.KroneckerDirectData.N143Part07
public import ENT.Pilot.KroneckerDirectData.N143Part08
public import ENT.Certificate.KroneckerDirectSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_143 : PackedFamily 143 := by
  intro k hk0 hk2
  have hkmax : k ≤ 71 := by omega
  interval_cases k
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k1_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k2_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k3_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k4_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k5_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k6_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k7_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k8_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k9_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k10_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k11_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k12_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k13_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k14_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k15_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k16_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k17_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k18_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k19_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k20_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k21_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k22_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k23_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k24_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k25_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k26_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k27_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k28_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k29_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k30_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k31_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k32_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k33_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k34_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k35_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k36_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k37_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k38_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k39_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k40_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k41_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k42_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k43_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k44_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k45_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k46_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k47_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k48_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k49_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k50_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k51_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k52_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k53_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k54_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k55_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k56_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k57_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k58_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k59_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k60_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k61_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k62_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k63_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k64_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k65_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k66_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k67_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k68_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k69_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k70_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n143k71_exists

end ENT.FiniteCertificates
