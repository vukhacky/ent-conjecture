module

public import ENT.Certificate.PureSoundness
public import ENT.Certificate.Family
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CertificateBridge

/-! A small public interface for large certificate families. Computational
modules may hide their literal arrays and export only exact existential
acceptance witnesses. Soundness still ties those witnesses to the actual
spline, derivative polynomial and reflected half-cell domain. -/

@[expose] public section
set_option autoImplicit false

open ENT.Certificate

namespace ENT.Spline

noncomputable section

theorem target_nonneg_of_cellConclusion (c : CellData) (hc : CellConclusion c)
    (n k : ℕ) (hcn : c.n = n) (hck : c.k = k) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ if 2 * k + 1 = n then (1 / 2 : ℝ) else 1) :
    0 ≤ targetPolynomial n k s := by
  rcases hc with ⟨_, _, _, hhalf, _, _, htarget⟩
  simp only [hcn, hck] at hhalf htarget
  have hw : width c = if 2 * k + 1 = n then (1 / 2 : ℝ) else 1 := by
    by_cases hf : c.halfCell = true
    · simp [width, hf, hhalf.mp hf]
    · have hcenter : ¬2 * k + 1 = n := fun h => hf (hhalf.mpr h)
      simp [width, hf, hcenter]
  exact htarget s hs0 (by rw [hw]; exact hs1)

theorem cellwiseCurvature_of_pure_family (n : ℕ) (hn : 4 ≤ n)
    (check : Pure.CellData → Bool)
    (hsound : ∀ c : Pure.CellData, check c = true → CellConclusion (Pure.toSemanticData c))
    (hfamily : PureCellFamily check n) : CellwiseCurvature n := by
  intro k hk s hs0 hs1
  by_cases hk0 : k = 0
  · subst k
    have hnot : ¬2 * 0 + 1 = n := by omega
    exact targetPolynomial_edge_nonneg n hn s hs0 (by simpa only [if_neg hnot] using hs1)
  · obtain ⟨c, hcn, hck, hc⟩ := hfamily k (by omega) hk
    exact target_nonneg_of_cellConclusion (Pure.toSemanticData c) (hsound c hc)
      n k hcn hck s hs0 hs1

theorem cellwiseCurvature_of_pure_prop_family (n : ℕ) (hn : 4 ≤ n)
    (valid : Pure.CellData → Prop)
    (hsound : ∀ c : Pure.CellData, valid c → CellConclusion (Pure.toSemanticData c))
    (hfamily : PurePropCellFamily valid n) : CellwiseCurvature n := by
  intro k hk s hs0 hs1
  by_cases hk0 : k = 0
  · subst k
    have hnot : ¬2 * 0 + 1 = n := by omega
    exact targetPolynomial_edge_nonneg n hn s hs0 (by simpa only [if_neg hnot] using hs1)
  · obtain ⟨c, hcn, hck, hc⟩ := hfamily k (by omega) hk
    exact target_nonneg_of_cellConclusion (Pure.toSemanticData c) (hsound c hc)
      n k hcn hck s hs0 hs1

end
end ENT.Spline
