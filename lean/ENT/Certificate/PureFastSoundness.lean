module

public import ENT.Certificate.PureFast
public import ENT.Certificate.FastChecker
public import ENT.Certificate.PureSoundness

/-! Exact semantic adapter for the import-light direct-binomial checker. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.Certificate.PureFast

theorem binomialPowerCoeffs_eq (a : ℤ) (m : ℕ) :
    binomialPowerCoeffs a m = ENT.Certificate.binomialPowerCoeffs a m := rfl

theorem fastSplineCoeffsAux_eq (n k m : ℕ) :
    fastSplineCoeffsAux n k m = ENT.Certificate.fastSplineCoeffsAux n k m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [fastSplineCoeffsAux, ENT.Certificate.fastSplineCoeffsAux,
        Pure.dense_add_eq, Pure.dense_scale_eq, binomialPowerCoeffs_eq, ih]

theorem fastSplineCoeffs_eq (n k : ℕ) :
    fastSplineCoeffs n k = ENT.Certificate.fastSplineCoeffs n k :=
  fastSplineCoeffsAux_eq n k (k + 1)

theorem arithmetic_iff (c : Pure.CellData) :
    FastCellArithmeticValid c ↔ ENT.Certificate.FastCellArithmeticValid (Pure.toSemanticData c) := by
  simp only [FastCellArithmeticValid, ENT.Certificate.FastCellArithmeticValid,
    Pure.toSemanticData, fastSplineCoeffs_eq, Pure.curvature_eq, Pure.halfTransform_eq]
  rfl

theorem fastCheckCell_eq_semantic (c : Pure.CellData) :
    fastCheckCell c = ENT.Certificate.fastCheckCell (Pure.toSemanticData c) := by
  unfold fastCheckCell ENT.Certificate.fastCheckCell
  rw [Pure.bernsteinCheck_eq]
  congr 1
  exact decide_eq_decide.mpr (arithmetic_iff c)

theorem fastCheckCell_sound (c : Pure.CellData) (hc : fastCheckCell c = true) :
    ENT.Certificate.CellConclusion (Pure.toSemanticData c) := by
  apply ENT.Certificate.fastCheckCell_sound
  rw [← fastCheckCell_eq_semantic]
  exact hc

end ENT.Certificate.PureFast
