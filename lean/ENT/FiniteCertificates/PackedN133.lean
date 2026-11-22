module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerDirectData.N133Part00
public import ENT.Pilot.KroneckerDirectData.N133Part01
public import ENT.Pilot.KroneckerDirectData.N133Part02
public import ENT.Pilot.KroneckerDirectData.N133Part03
public import ENT.Pilot.KroneckerDirectData.N133Part04
public import ENT.Pilot.KroneckerDirectData.N133Part05
public import ENT.Pilot.KroneckerDirectData.N133Part06
public import ENT.Pilot.KroneckerDirectData.N133Part07
public import ENT.Pilot.KroneckerDirectData.N133Part08
public import ENT.Certificate.KroneckerDirectSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_133 : PackedFamily 133 := by
  intro k hk0 hk2
  have hkmax : k ≤ 66 := by omega
  interval_cases k
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k1_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k2_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k3_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k4_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k5_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k6_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k7_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k8_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k9_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k10_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k11_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k12_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k13_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k14_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k15_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k16_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k17_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k18_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k19_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k20_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k21_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k22_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k23_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k24_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k25_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k26_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k27_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k28_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k29_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k30_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k31_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k32_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k33_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k34_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k35_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k36_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k37_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k38_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k39_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k40_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k41_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k42_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k43_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k44_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k45_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k46_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k47_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k48_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k49_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k50_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k51_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k52_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k53_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k54_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k55_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k56_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k57_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k58_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k59_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k60_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k61_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k62_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k63_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k64_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k65_exists
  · exact Certificate.KroneckerDirect.exists_valid_to_pure ENT.Pilot.KroneckerDirectData.n133k66_exists

end ENT.FiniteCertificates
