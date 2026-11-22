module

public import ENT.Pilot.FiniteRange7To17
public import ENT.Pilot.N18To20PureBatch
public import ENT.Certificate.PureSoundness
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CurvatureData

/-! Complete cell coverage for dimensions 7–20 and its relation to the diagonal spline. -/

@[expose] public section
set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory

namespace ENT.Pilot
noncomputable section

private theorem cellwise_of_pureBatchFamily (n : ℕ) (hn : 4 ≤ n)
    (hfamily : ∀ k : ℕ, 0 < k → 2 * k < n →
      ∃ c : Pure.CellData, c.n = n ∧ c.k = k ∧ Pure.checkCell c = true) :
    CellwiseCurvature n := by
  intro k hk s hs0 hs1
  by_cases hk0 : k = 0
  · subst k
    have hnot : ¬2 * 0 + 1 = n := by omega
    exact targetPolynomial_edge_nonneg n hn s hs0 (by simpa only [if_neg hnot] using hs1)
  · obtain ⟨c, hcn, hck, hcheck⟩ := hfamily k (by omega) hk
    have h := Pure.checkCell_sound c hcheck
    rcases h with ⟨_, _, _, hhalf, _, _, htarget⟩
    change (c.halfCell = true ↔ 2 * c.k + 1 = c.n) at hhalf
    change ∀ s : ℝ, 0 ≤ s → s ≤ width (Pure.toSemanticData c) →
      0 ≤ targetPolynomial c.n c.k s at htarget
    rw [hcn, hck] at hhalf htarget
    have hw : width (Pure.toSemanticData c) =
        if 2 * k + 1 = n then (1 / 2 : ℝ) else 1 := by
      by_cases hf : c.halfCell = true
      · simp [width, Pure.toSemanticData, hf, hhalf.mp hf]
      · have hcenter : ¬2 * k + 1 = n := fun h => hf (hhalf.mpr h)
        simp [width, Pure.toSemanticData, hf, hcenter]
    exact htarget s hs0 (by rw [hw]; exact hs1)

theorem dimension18_cellwise_from_pure_batch : CellwiseCurvature 18 := by
  apply cellwise_of_pureBatchFamily 18 (by decide)
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 8 := by omega
  interval_cases k
  · exact batchN18K1_exists
  · exact batchN18K2_exists
  · exact batchN18K3_exists
  · exact batchN18K4_exists
  · exact batchN18K5_exists
  · exact batchN18K6_exists
  · exact batchN18K7_exists
  · exact batchN18K8_exists

theorem dimension19_cellwise_from_pure_batch : CellwiseCurvature 19 := by
  apply cellwise_of_pureBatchFamily 19 (by decide)
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 9 := by omega
  interval_cases k
  · exact batchN19K1_exists
  · exact batchN19K2_exists
  · exact batchN19K3_exists
  · exact batchN19K4_exists
  · exact batchN19K5_exists
  · exact batchN19K6_exists
  · exact batchN19K7_exists
  · exact batchN19K8_exists
  · exact batchN19K9_exists

theorem dimension20_cellwise_from_pure_batch : CellwiseCurvature 20 := by
  apply cellwise_of_pureBatchFamily 20 (by decide)
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 9 := by omega
  interval_cases k
  · exact batchN20K1_exists
  · exact batchN20K2_exists
  · exact batchN20K3_exists
  · exact batchN20K4_exists
  · exact batchN20K5_exists
  · exact batchN20K6_exists
  · exact batchN20K7_exists
  · exact batchN20K8_exists
  · exact batchN20K9_exists

theorem cellwise_curvature_seven_through_twenty (n : ℕ) (hn0 : 7 ≤ n) (hn1 : n ≤ 20) :
    CellwiseCurvature n := by
  by_cases hn17 : n ≤ 17
  · exact cellwise_curvature_seven_through_seventeen n hn0 hn17
  have hn18 : 18 ≤ n := by omega
  interval_cases n
  · exact dimension18_cellwise_from_pure_batch
  · exact dimension19_cellwise_from_pure_batch
  · exact dimension20_cellwise_from_pure_batch

theorem potential_expectation_le_seven_through_twenty (n : ℕ) (hn0 : 7 ≤ n) (hn1 : n ≤ 20)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential n x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential n x ∂projectionLaw (diagonal n) :=
  diagonalSplinePotential_expectation_le n (by omega)
    (cellwise_curvature_seven_through_twenty n hn0 hn1) a ha

end
end ENT.Pilot
