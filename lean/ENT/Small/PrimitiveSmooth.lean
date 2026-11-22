module

public import ENT.Small.BoxPrimitive
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Taylor

/-! Regularity and derivative semantics of actual interval primitives. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace ENT.Small

noncomputable section

theorem hasDerivAt_intervalPrimitive {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {x : ℝ}
    (hfc : ContinuousAt f x) (hfm : StronglyMeasurableAtFilter f (𝓝 x)) :
    HasDerivAt (fun y => ∫ t in 0..y, f t) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf 0 x) hfm hfc

theorem contDiffOn_intervalPrimitive {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {s : Set ℝ} (hs : IsOpen s)
    (k : ℕ) (hfc : ContDiffOn ℝ k f s) :
    ContDiffOn ℝ (k + 1 : ℕ) (fun y => ∫ t in 0..y, f t) s := by
  have hd : ∀ x ∈ s, HasDerivAt (fun y => ∫ t in 0..y, f t) (f x) x := by
    intro x hx
    have hc : ContinuousAt f x := (hfc.continuousOn x hx).continuousAt (hs.mem_nhds hx)
    exact hasDerivAt_intervalPrimitive hf hc (ContinuousOn.stronglyMeasurableAtFilter hs hfc.continuousOn x hx)
  rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen hs]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · simp
  · exact hfc.congr (fun x hx => (hd x hx).deriv)

theorem contDiffOn_boxPrimitive {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {s : Set ℝ} (hs : IsOpen s)
    (k n : ℕ) (hfc : ContDiffOn ℝ k f s) :
    ContDiffOn ℝ (k + n : ℕ) (boxPrimitive f n) s := by
  induction n with
  | zero => simpa only [Nat.add_zero, boxPrimitive_zero] using hfc
  | succ n ih =>
      simpa only [Nat.add_assoc, boxPrimitive] using contDiffOn_intervalPrimitive
        (intervalIntegrable_boxPrimitive hf n) hs (k + n) ih

theorem contDiff_boxPrimitive_succ {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (n : ℕ) :
    ContDiff ℝ n (boxPrimitive f (n + 1)) := by
  induction n with
  | zero => exact contDiff_zero.mpr (continuous_boxPrimitive_succ hf 0)
  | succ n ih =>
      rw [← contDiffOn_univ]
      simpa only [boxPrimitive] using contDiffOn_intervalPrimitive
        (intervalIntegrable_boxPrimitive hf (n + 1)) isOpen_univ n ih.contDiffOn

theorem deriv_boxPrimitive_succ_succ {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (n : ℕ) :
    deriv (boxPrimitive f (n + 2)) = boxPrimitive f (n + 1) := by
  funext x
  exact (hasDerivAt_boxPrimitive_succ_succ hf n x).deriv

theorem iteratedDeriv_boxPrimitive_three_one {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) :
    iteratedDeriv 1 (boxPrimitive f 3) = boxPrimitive f 2 := by
  simpa only [iteratedDeriv_one] using deriv_boxPrimitive_succ_succ hf 1

theorem iteratedDeriv_boxPrimitive_three_two {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) :
    iteratedDeriv 2 (boxPrimitive f 3) = boxPrimitive f 1 := by
  rw [iteratedDeriv_succ, iteratedDeriv_boxPrimitive_three_one hf]
  exact deriv_boxPrimitive_succ_succ hf 0

theorem iteratedDeriv_boxPrimitive_three_three {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {s : Set ℝ} (hs : IsOpen s)
    (hfc : ContinuousOn f s) {x : ℝ} (hx : x ∈ s) :
    iteratedDeriv 3 (boxPrimitive f 3) x = f x := by
  rw [iteratedDeriv_succ, iteratedDeriv_boxPrimitive_three_two hf]
  have hc := (hfc x hx).continuousAt (hs.mem_nhds hx)
  exact (hasDerivAt_intervalPrimitive hf hc (ContinuousOn.stronglyMeasurableAtFilter hs hfc x hx)).deriv

theorem iteratedDeriv_boxPrimitive_three_four {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {s : Set ℝ} (hs : IsOpen s)
    (hfc : ContinuousOn f s) {x : ℝ} (hx : x ∈ s) :
    iteratedDeriv 4 (boxPrimitive f 3) x = deriv f x := by
  have heq : iteratedDeriv 3 (boxPrimitive f 3) =ᶠ[𝓝 x] f := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact iteratedDeriv_boxPrimitive_three_three hf hs hfc hy
  rw [iteratedDeriv_succ]
  exact heq.deriv_eq

theorem iteratedDeriv_boxPrimitive_three_five {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {s : Set ℝ} (hs : IsOpen s)
    (hfc : ContinuousOn f s) {x : ℝ} (hx : x ∈ s) :
    iteratedDeriv 5 (boxPrimitive f 3) x = deriv (deriv f) x := by
  have heq : iteratedDeriv 4 (boxPrimitive f 3) =ᶠ[𝓝 x] deriv f := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact iteratedDeriv_boxPrimitive_three_four hf hs hfc hy
  rw [iteratedDeriv_succ]
  exact heq.deriv_eq

end
end ENT.Small
