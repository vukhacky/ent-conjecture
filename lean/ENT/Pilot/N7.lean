module

public import ENT.Pilot.N7Cell0
public import ENT.Pilot.N7Cell1
public import ENT.Pilot.N7Cell2
public import ENT.Pilot.N7Cell3
public import Mathlib.Tactic.IntervalCases

/-! Polynomial certificates for all reflected spline cells in dimension seven. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate

namespace ENT.Pilot

theorem dimension7_polynomial_certificate (k : ℕ) (hk : 2 * k < 7)
    (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s ≤ if 2 * k + 1 = 7 then (1 / 2 : ℝ) else 1) :
    0 ≤ targetPolynomial 7 k s := by
  have hkle : k ≤ 3 := by omega
  interval_cases k
  · exact n7k0_target_nonneg s hs0 (by simpa using hs1)
  · exact n7k1_target_nonneg s hs0 (by simpa using hs1)
  · exact n7k2_target_nonneg s hs0 (by simpa using hs1)
  · exact n7k3_target_nonneg s hs0 (by simpa using hs1)

theorem dimension7_four_cell_conclusions :
    CellConclusion n7k0Data ∧ CellConclusion n7k1Data ∧
      CellConclusion n7k2Data ∧ CellConclusion n7k3Data :=
  ⟨n7k0_conclusion, n7k1_conclusion, n7k2_conclusion, n7k3_conclusion⟩

end ENT.Pilot
