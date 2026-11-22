module

public import ENT.Certificate.CompleteChecker

/-! Certificate of the polynomial identities and Bernstein coefficient inequalities on this spline cell. -/
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open ENT.Certificate

namespace ENT.Pilot

def completeN8K1Data : CellData where
  n := 8
  k := 1
  degreeBound := 22
  halfCell := false
  pCoeffs := [1, 7, 21, 35, 35, 21, 7, -7]
  rCoeffs := [6832, 122080, 1028496, 5425728, 19211920, 46818912, 80986416, 107909760, 133523040, 178617152, 225078560, 197831424, 59566752, -84054208, -102109728, -32796288, 9269232, 7474656, -3495856, -768320, -115248, 230496, -38416]
  transformedCoeffs := [6832, 122080, 1028496, 5425728, 19211920, 46818912, 80986416, 107909760, 133523040, 178617152, 225078560, 197831424, 59566752, -84054208, -102109728, -32796288, 9269232, 7474656, -3495856, -768320, -115248, 230496, -38416]
  bernsteinNumerators := [6832, 272384, 5170368, 62153728, 530057472, 3403481088, 17050887168, 68213620608, 221430875904, 589947893248, 1300809509888, 2388022425600, 3664349753344, 4708003700736, 5058939110400, 4522876538880, 3328134684672, 1978755072000, 923565031424, 323881205760, 79621914624, 12120399872, 849723392]

theorem completeN8K1_accepts : checkCell completeN8K1Data = true := by
  decide +kernel

theorem completeN8K1_conclusion : CellConclusion completeN8K1Data :=
  checkCell_sound _ completeN8K1_accepts

end ENT.Pilot
