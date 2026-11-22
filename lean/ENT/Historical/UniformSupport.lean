module

public import ENT.Basic.ProjectionSupport
public import Mathlib.MeasureTheory.Measure.Support

/-! Exact topological support of the continuous uniform law. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Topology

namespace ENT

theorem uniformUnit_support : uniformUnit.support = Icc (-1 : ℝ) 1 := by
  have hscaled : uniformUnit.support =
      (volume.restrict (Icc (-1 : ℝ) 1)).support := by
    ext x
    simp only [Measure.mem_support_iff_forall, uniformUnit, smul_apply,
      smul_eq_mul, ENNReal.mul_pos_iff]
    norm_num
  rw [hscaled]
  apply Subset.antisymm
  · exact (Measure.support_restrict_subset (μ := (volume : Measure ℝ))).trans
      (by simpa only [isClosed_Icc.closure_eq] using
        inter_subset_left (s := Icc (-1 : ℝ) 1) (t := volume.support))
  · have hin : Ioo (-1 : ℝ) 1 ⊆ (volume.restrict (Icc (-1 : ℝ) 1)).support := by
      intro x hx
      apply Measure.interior_inter_support
      constructor
      · simpa only [interior_Icc] using hx
      · rw [Measure.support_eq_univ]
        trivial
    have hc := closure_minimal hin Measure.isClosed_support
    simpa only [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] using hc

end ENT
