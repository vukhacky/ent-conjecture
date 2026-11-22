module

public import ENT.Comparison.ConvexCrossing
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! A monotone likelihood ratio up to a cap gives the two crossings needed
for convex order.  Mass and first moment are explicit, integrable quantities. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Historical
noncomputable section

theorem monotoneOn_exists_threshold {r : ℝ → ℝ} {c v : ℝ}
    (hc : 0 < c) (hr : MonotoneOn r (Ioo 0 c)) :
    ∃ a ∈ Icc (0 : ℝ) c,
      (∀ x ∈ Ioo (0 : ℝ) a, r x ≤ v) ∧
      (∀ x ∈ Ioo a c, v ≤ r x) := by
  let A : Set ℝ := {x | x = 0 ∨ (x ∈ Ioo (0 : ℝ) c ∧ r x ≤ v)}
  have hAne : A.Nonempty := ⟨0, Or.inl rfl⟩
  have hAbdd : BddAbove A := ⟨c, by
    rintro x (rfl | ⟨hx, _⟩)
    · exact hc.le
    · exact hx.2.le⟩
  have ha0 : 0 ≤ sSup A := le_csSup hAbdd (Or.inl rfl)
  have hac : sSup A ≤ c := csSup_le hAne (by
    rintro x (rfl | ⟨hx, _⟩)
    · exact hc.le
    · exact hx.2.le)
  refine ⟨sSup A, ⟨ha0, hac⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyA, hxy⟩ := exists_lt_of_lt_csSup hAne hx.2
    rcases hyA with rfl | ⟨hy, hyr⟩
    · exact (not_lt_of_ge hx.1.le hxy).elim
    · exact (hr ⟨hx.1, lt_of_lt_of_le hx.2 hac⟩ hy hxy.le).trans hyr
  · intro x hx
    by_contra h
    have hxA : x ∈ A := Or.inr ⟨⟨lt_of_le_of_lt ha0 hx.1, hx.2⟩, (not_le.mp h).le⟩
    exact (not_le_of_gt hx.1) (le_csSup hAbdd hxA)

theorem convex_integral_le_of_capped_monotone_ratio
    {f g φ : ℝ → ℝ} {c s : ℝ} (hc : 0 < c) (hcs : c ≤ s)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x, x ∉ Icc (0 : ℝ) c → f x = 0)
    (hgsupp : ∀ x, x ∉ Icc (0 : ℝ) s → g x = 0)
    (hgpos : ∀ x ∈ Ioo (0 : ℝ) c, 0 < g x)
    (hratio : MonotoneOn (fun x => f x / g x) (Ioo (0 : ℝ) c))
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hxf : Integrable (fun x => x * f x) volume)
    (hxg : Integrable (fun x => x * g x) volume)
    (hφf : Integrable (fun x => φ x * f x) volume)
    (hφg : Integrable (fun x => φ x * g x) volume)
    (hmass : (∫ x, f x) = ∫ x, g x)
    (hmean : (∫ x, x * f x) = ∫ x, x * g x)
    (hφ : ConvexOn ℝ (Icc 0 s) φ) :
    (∫ x, φ x * f x) ≤ ∫ x, φ x * g x := by
  obtain ⟨a, ha, hlo, hhi⟩ := monotoneOn_exists_threshold hc hratio (v := 1)
  have hd : Integrable (fun x => g x - f x) volume := hg.sub hf
  have hxd : Integrable (fun x => x * (g x - f x)) volume := by
    convert hxg.sub hxf using 1
    ext x
    exact mul_sub _ _ _
  have hφd : Integrable (fun x => φ x * (g x - f x)) volume := by
    convert hφg.sub hφf using 1
    ext x
    exact mul_sub _ _ _
  have hmass0 : (∫ x, g x - f x) = 0 := by rw [integral_sub hg hf, hmass, sub_self]
  have hmean0 : (∫ x, x * (g x - f x)) = 0 := by
    simp only [mul_sub]
    rw [integral_sub hxg hxf, hmean, sub_self]
  have hlop : ∀ x ∈ Ioo (0 : ℝ) a, f x ≤ g x := by
    intro x hx
    exact (div_le_one (hgpos x ⟨hx.1, lt_of_lt_of_le hx.2 ha.2⟩)).mp (hlo x hx)
  have hhip : ∀ x ∈ Ioo a c, g x ≤ f x := by
    intro x hx
    exact (one_le_div (hgpos x ⟨lt_of_le_of_lt ha.1 hx.1, hx.2⟩)).mp (hhi x hx)
  have hout0 : ∀ x, x < 0 → g x - f x = 0 := by
    intro x hx
    rw [hfsupp x (by intro h; exact (not_le_of_gt hx) h.1),
      hgsupp x (by intro h; exact (not_le_of_gt hx) h.1), sub_self]
  have houtc : ∀ x, c < x → 0 ≤ g x - f x := by
    intro x hx
    rw [hfsupp x (by intro h; exact (not_le_of_gt hx) h.2), sub_zero]
    exact hg0 x
  have hnonneg : 0 ≤ ∫ x, φ x * (g x - f x) := by
    rcases lt_or_eq_of_le ha.2 with hac | hac
    · apply Comparison.integral_convex_nonneg_of_two_crossings_support
        hφ ⟨ha.1, ha.2.trans hcs⟩ ⟨hc.le, hcs⟩ hac
        (d := fun x => g x - f x) (X := id)
      · filter_upwards [] with x hx
        by_contra hnot
        have hxnot : x ∉ Icc (0 : ℝ) c := fun hx' => hnot ⟨hx'.1, hx'.2.trans hcs⟩
        exact hx (by rw [hfsupp x hxnot, hgsupp x hnot, sub_self])
      · exact hd
      · exact hxd
      · exact hφd
      · exact hmass0
      · exact hmean0
      · filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne a, volume.ae_ne c] with x hx0 hxa hxc
        intro hx
        change x ≤ a ∨ c ≤ x at hx
        rcases hx with hxa' | hxc'
        · rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
          · rw [hout0 x hxneg]
          · exact sub_nonneg.mpr (hlop x ⟨hxpos, lt_of_le_of_ne hxa' hxa⟩)
        · exact houtc x (lt_of_le_of_ne hxc' (Ne.symm hxc))
      · filter_upwards [volume.ae_ne a, volume.ae_ne c] with x hxa hxc
        intro hx
        change a ≤ x ∧ x ≤ c at hx
        exact sub_nonpos.mpr (hhip x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),
          lt_of_le_of_ne hx.2 hxc⟩)
    · have hnonnegd : ∀ᵐ x ∂volume, 0 ≤ g x - f x := by
        filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne c] with x hx0 hxc
        rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
        · rw [hout0 x hxneg]
        · rcases lt_or_gt_of_ne hxc with hxlt | hxgt
          · exact sub_nonneg.mpr (hlop x ⟨hxpos, hac ▸ hxlt⟩)
          · exact houtc x hxgt
      have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonnegd hd).mp hmass0
      have hzero' : (fun x => φ x * (g x - f x)) =ᵐ[volume] 0 := by
        filter_upwards [hzero] with x hx
        simp only [Pi.zero_apply] at hx ⊢
        rw [hx, mul_zero]
      rw [integral_congr_ae hzero']
      simp
  simpa only [mul_sub, integral_sub hφg hφf, sub_nonneg] using hnonneg

end
end ENT.Historical
