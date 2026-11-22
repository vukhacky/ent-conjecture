module

public import ENT.Small.ThreeDensity
public import ENT.Small.BoxFormula
public import ENT.Spline.SupportInterior
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import ENT.Small.EndpointLog
public import ENT.Base.TwoEntropy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import ENT.Small.EnclosuresFour
public import ENT.Small.PrimitiveSmooth
public import ENT.Small.PrimitiveKernel
public import ENT.Small.LogIntegrals
public import ENT.Comparison.DensityExpectations
public import ENT.Small.TaylorFourth
public import ENT.Small.TaylorSecond
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Analytic proof of the entropy comparison in dimension four. -/

/-! Exact polynomial pieces of the genuine n=4 diagonal density. -/

@[expose] public section

set_option autoImplicit false

open Set

namespace ENT.Small

noncomputable section

theorem sqrt_four_eq_two : Real.sqrt (4 : ℝ) = 2 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)

theorem unitSumSplineDensity_four_left {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Spline.unitSumSplineDensity 4 x = x ^ 3 / 6 := by
  have h := Spline.unnormalizedSpline_eq_piece 4 0 (by norm_num) (by norm_num) x hx.1 hx.2
  norm_num only [Nat.cast_zero, zero_add] at h
  rw [Spline.unitSumSplineDensity, h, Certificate.splinePiece_edge]
  norm_num
  ring

theorem unitSumSplineDensity_four_middle {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    Spline.unitSumSplineDensity 4 x = (x ^ 3 - 4 * (x - 1) ^ 3) / 6 := by
  have h := Spline.unnormalizedSpline_eq_piece 4 1 (by norm_num) (by norm_num) (x - 1)
    (by linarith [hx.1]) (by linarith [hx.2])
  norm_num only [Nat.cast_one, add_sub_cancel] at h
  rw [Spline.unitSumSplineDensity, h]
  norm_num [Certificate.splinePiece, Finset.sum_range_succ, Nat.choose]
  ring

theorem diagonalSplineDensity_four_center {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Spline.diagonalSplineDensity 4 x = 2 / 3 - x ^ 2 + x ^ 3 / 2 := by
  have ht : (2 - x) ∈ Icc (1 : ℝ) 2 := by constructor <;> linarith [hx.1, hx.2]
  unfold Spline.diagonalSplineDensity
  norm_num only [Nat.cast_ofNat]
  rw [sqrt_four_eq_two]
  have heq : ((4 : ℝ) - 2 * x) / 2 = 2 - x := by ring
  rw [heq, unitSumSplineDensity_four_middle ht]
  ring

theorem diagonalSplineDensity_four_outer {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    Spline.diagonalSplineDensity 4 x = (2 - x) ^ 3 / 6 := by
  have ht : (2 - x) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  unfold Spline.diagonalSplineDensity
  norm_num only [Nat.cast_ofNat]
  rw [sqrt_four_eq_two]
  have heq : ((4 : ℝ) - 2 * x) / 2 = 2 - x := by ring
  rw [heq, unitSumSplineDensity_four_left ht]
  ring

theorem diagonalSplineDensity_four_cut : Spline.diagonalSplineDensity 4 1 = (1 : ℝ) / 6 := by
  rw [diagonalSplineDensity_four_center (by constructor <;> norm_num)]
  norm_num

theorem diagonalSplineDensity_four_tenth :
    Spline.diagonalSplineDensity 4 (1 / 10) = (3943 : ℝ) / 6000 := by
  rw [diagonalSplineDensity_four_center (by constructor <;> norm_num)]
  norm_num

end
end ENT.Small

/-! Four uniform integrations and the even fourth-primitive formula. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Small

noncomputable section

theorem integral_projection_four_eq_boxAverage (a : Fin 4 → ℝ)
    (ha : ∀ i, 0 < a i) {f : ℝ → ℝ} (hf : Integrable f) :
    (∫ x, f x ∂projectionLaw a) =
      boxAverage (a 0) (boxAverage (a 1) (boxAverage (a 2) (boxAverage (a 3) f))) 0 := by
  have hi := integrable_projection_of_integrable a 0 (ha 0) hf
  rw [projectionLaw_eq_conv_remove a 0] at hi ⊢
  rw [integral_conv hi, (measurableEmbedding_mulLeft₀ (ha 0).ne').integral_map]
  change (∫ u, (∫ y, f (a 0 * u + y) ∂projectionLaw (removeCoefficient a 0)) ∂uniformUnit) = _
  unfold boxAverage
  simp only [zero_add]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  dsimp only
  have h := integral_projection_three_eq_boxAverage (removeCoefficient a 0)
    (fun i => ha (Fin.succ i)) (hf.comp_add_left (a 0 * u))
  rw [h]
  unfold boxAverage
  simp only [zero_add]
  congr 1
  funext v
  congr 1
  funext w
  congr 1
  funext z
  change f (a 0 * u + (a 1 * v + a 2 * w + a 3 * z)) =
    f (a 0 * u + a 1 * v + a 2 * w + a 3 * z)
  congr 1
  ring

theorem boxAverage_four_primitive {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b)
    {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (x : ℝ) :
    boxAverage a (boxAverage b (boxAverage c (boxAverage d f))) x =
      ((2 * a) * (2 * b) * (2 * c) * (2 * d))⁻¹ *
        centralDifference d (centralDifference c (centralDifference b
          (centralDifference a (boxPrimitive f 4)))) x := by
  have hthree : boxAverage b (boxAverage c (boxAverage d f)) = fun y =>
      ((2 * b) * (2 * c) * (2 * d))⁻¹ *
        centralDifference d (centralDifference c (centralDifference b (boxPrimitive f 3))) y := by
    funext y
    exact boxAverage_three_primitive hf hb hc hd y
  have hfour : boxAverage a (boxPrimitive f 3) =
      fun y => (2 * a)⁻¹ * centralDifference a (boxPrimitive f 4) y := by
    funext y
    exact boxAverage_primitive hf ha 3 y
  have hlin (u k : ℝ) (g : ℝ → ℝ) :
      boxAverage u (fun y => k * g y) = fun y => k * boxAverage u g y := by
    funext y
    exact boxAverage_const_mul u k g y
  have hcomm (u v : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
      boxAverage u (centralDifference v g) = centralDifference v (boxAverage u g) := by
    funext y
    exact boxAverage_comm_centralDifference u v hg y
  have hdlin (u k : ℝ) (g : ℝ → ℝ) :
      centralDifference u (fun y => k * g y) = fun y => k * centralDifference u g y := by
    funext y
    exact centralDifference_const_mul u k g y
  rw [hthree, hlin,
    hcomm a d _ (continuous_centralDifference c
      (continuous_centralDifference b (continuous_boxPrimitive_succ hf 2))),
    hcomm a c _ (continuous_centralDifference b (continuous_boxPrimitive_succ hf 2)),
    hcomm a b _ (continuous_boxPrimitive_succ hf 2), hfour, hdlin, hdlin, hdlin]
  simp only [mul_inv]
  ring

def fourBoxNumerator (F : ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  F (a + b + c + d) - F (-a + b + c + d) - F (a - b + c + d) -
    F (a + b - c + d) - F (a + b + c - d) + F (-a - b + c + d) +
      F (-a + b - c + d) + F (-a + b + c - d)

theorem centralDifference_odd_of_even {F : ℝ → ℝ} (hF : Function.Even F) (a : ℝ) :
    Function.Odd (centralDifference a F) := by
  intro x
  unfold centralDifference
  have h1 : F (-x + a) = F (x - a) := by
    convert hF (x - a) using 1 <;> congr 1 <;> ring
  have h2 : F (-x - a) = F (x + a) := by
    convert hF (x + a) using 1 <;> congr 1 <;> ring
  rw [h1, h2]
  ring

theorem centralDifference_four_even {F : ℝ → ℝ} (hF : Function.Even F) (a b c d : ℝ) :
    centralDifference d (centralDifference c (centralDifference b (centralDifference a F))) 0 =
      2 * fourBoxNumerator F a b c d := by
  rw [centralDifference_three_odd (centralDifference_odd_of_even hF a)]
  unfold centralDifference fourBoxNumerator
  ring_nf

theorem integral_projection_four_primitive (a : Fin 4 → ℝ) (ha : ∀ i, 0 < a i)
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f) :
    (∫ x, f x ∂projectionLaw a) =
      fourBoxNumerator (boxPrimitive f 4) (a 0) (a 1) (a 2) (a 3) /
        (8 * a 0 * a 1 * a 2 * a 3) := by
  have he : Function.Even (boxPrimitive f 4) := by
    intro x
    have h := boxPrimitive_parity heven 4 x
    norm_num only [pow_succ, pow_zero, mul_one, neg_mul, one_mul, neg_neg] at h
    exact h
  rw [integral_projection_four_eq_boxAverage a ha hf,
    boxAverage_four_primitive (fun _ _ => hf.intervalIntegrable)
      (ha 0).ne' (ha 1).ne' (ha 2).ne' (ha 3).ne', centralDifference_four_even he]
  field_simp
  ring

end
end ENT.Small

/-! Derivative and near-origin bounds for the genuine four-dimensional potential. -/

@[expose] public section

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace ENT.Small

noncomputable section

def fourCenterDensity (x : ℝ) : ℝ := 2 / 3 - x ^ 2 + x ^ 3 / 2

theorem fourCenterDensity_ge_sixth {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (1 : ℝ) / 6 ≤ fourCenterDensity x := by
  have hx2 : x ^ 2 ≤ x := by nlinarith [hx.1, hx.2]
  have hpos : 0 ≤ (1 - x) * (1 + x - x ^ 2) :=
    mul_nonneg (by linarith [hx.2]) (by nlinarith)
  unfold fourCenterDensity
  nlinarith

theorem hasDerivAt_fourCenterDensity (x : ℝ) :
    HasDerivAt fourCenterDensity (-2 * x + 3 * x ^ 2 / 2) x := by
  have h := ((hasDerivAt_const x ((2 : ℝ) / 3)).sub ((hasDerivAt_id x).pow 2)).add
    (((hasDerivAt_id x).pow 3).div_const 2)
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

theorem hasDerivAt_diagonalSplineDensity_four_center {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (Spline.diagonalSplineDensity 4) (-2 * x + 3 * x ^ 2 / 2) x := by
  have heq : Spline.diagonalSplineDensity 4 =ᶠ[𝓝 x] fourCenterDensity := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact diagonalSplineDensity_four_center ⟨hy.1.le, hy.2.le⟩
  exact (hasDerivAt_fourCenterDensity x).congr_of_eventuallyEq heq

theorem hasDerivAt_diagonalSplineDensity_four_outer {x : ℝ} (hx : x ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (Spline.diagonalSplineDensity 4) (-(2 - x) ^ 2 / 2) x := by
  have heq : Spline.diagonalSplineDensity 4 =ᶠ[𝓝 x] (fun y : ℝ => (2 - y) ^ 3 / 6) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact diagonalSplineDensity_four_outer ⟨hy.1.le, hy.2.le⟩
  have h := (((hasDerivAt_const x (2 : ℝ)).sub (hasDerivAt_id x)).pow 3).div_const 6
  have hp : HasDerivAt (fun y : ℝ => (2 - y) ^ 3 / 6) (-(2 - x) ^ 2 / 2) x := by
    convert h using 1
    · rfl
    · simp only [Pi.sub_apply, id_eq]
      ring
  exact hp.congr_of_eventuallyEq heq

theorem hasDerivAt_diagonalSplinePotential_four_center {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (Spline.diagonalSplinePotential 4)
      ((2 * x - 3 * x ^ 2 / 2) / fourCenterDensity x) x := by
  have hq : Spline.diagonalSplineDensity 4 x ≠ 0 := by
    rw [diagonalSplineDensity_four_center ⟨hx.1.le, hx.2.le⟩]
    exact (lt_of_lt_of_le (by norm_num) (fourCenterDensity_ge_sixth ⟨hx.1.le, hx.2.le⟩)).ne'
  have h := ((hasDerivAt_diagonalSplineDensity_four_center hx).log hq).neg
  convert h using 1
  · rfl
  · rw [diagonalSplineDensity_four_center ⟨hx.1.le, hx.2.le⟩]
    unfold fourCenterDensity
    ring

theorem hasDerivAt_diagonalSplinePotential_four_outer {x : ℝ} (hx : x ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (Spline.diagonalSplinePotential 4) (3 / (2 - x)) x := by
  have hgap : 2 - x ≠ 0 := by linarith [hx.2]
  have hq : Spline.diagonalSplineDensity 4 x ≠ 0 := by
    rw [diagonalSplineDensity_four_outer ⟨hx.1.le, hx.2.le⟩]
    exact div_ne_zero (pow_ne_zero 3 hgap) (by norm_num)
  have h := ((hasDerivAt_diagonalSplineDensity_four_outer hx).log hq).neg
  convert h using 1
  · rfl
  · rw [diagonalSplineDensity_four_outer ⟨hx.1.le, hx.2.le⟩]
    field_simp
    ring

theorem contDiffOn_diagonalSplinePotential_four (k : ℕ) (hk : k ≤ 2) :
    ContDiffOn ℝ k (Spline.diagonalSplinePotential 4) (Ioo (-2 : ℝ) 2) := by
  intro x hx
  have hxs : x ∈ Ioo (-Real.sqrt (4 : ℝ)) (Real.sqrt (4 : ℝ)) := by
    simpa only [sqrt_four_eq_two] using hx
  exact (Spline.contDiffAt_diagonalSplinePotential k 4 (by omega) x
    (Spline.diagonalSplineDensity_pos 4 (by norm_num) x hxs).ne').contDiffWithinAt

theorem deriv_diagonalSplinePotential_four_cut : deriv (Spline.diagonalSplinePotential 4) 1 = 3 := by
  have hdq := (Spline.contDiff_diagonalSplineDensity 1 4 (by norm_num)).differentiable (by norm_num) 1
  have hp := (hasDerivAt_fourCenterDensity 1).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  have hactual : HasDerivWithinAt (Spline.diagonalSplineDensity 4) (-(1 : ℝ) / 2) (Icc (0 : ℝ) 1) 1 := by
    convert hp.congr (fun y hy => diagonalSplineDensity_four_center hy)
      (diagonalSplineDensity_four_center (by constructor <;> norm_num)) using 1 <;> norm_num
  have hu := (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) 1 (by constructor <;> norm_num)
  have hvalue := (hactual.derivWithin hu).symm.trans (hdq.hasDerivAt.hasDerivWithinAt.derivWithin hu)
  have hq : Spline.diagonalSplineDensity 4 1 ≠ 0 := by rw [diagonalSplineDensity_four_cut]; norm_num
  have hv := (hdq.hasDerivAt.log hq).neg
  have hd := hv.deriv
  change deriv (Spline.diagonalSplinePotential 4) 1 = _ at hd
  rw [← hvalue, diagonalSplineDensity_four_cut] at hd
  norm_num at hd
  exact hd

theorem abs_deriv_diagonalSplinePotential_four_le {x : ℝ}
    (hx : x ∈ Icc ((3 : ℝ) / 4) (5 / 4)) :
    |deriv (Spline.diagonalSplinePotential 4) x| ≤ 4 := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have hx0 : 0 < x := by linarith [hx.1]
    rw [(hasDerivAt_diagonalSplinePotential_four_center ⟨hx0, hlt⟩).deriv]
    have hq := fourCenterDensity_ge_sixth ⟨hx0.le, hlt.le⟩
    have hqpos : 0 < fourCenterDensity x := by linarith
    have hx2 : x ^ 2 ≤ x := by nlinarith [hx0, hlt]
    have hnum0 : 0 ≤ 2 * x - 3 * x ^ 2 / 2 := by nlinarith
    have hnum : 2 * x - 3 * x ^ 2 / 2 ≤ 2 / 3 := by nlinarith [sq_nonneg (x - 2 / 3)]
    rw [abs_of_nonneg (div_nonneg hnum0 hqpos.le)]
    apply (div_le_iff₀ hqpos).mpr
    linarith
  · subst x
    rw [deriv_diagonalSplinePotential_four_cut]
    norm_num
  · have hx2 : x < 2 := by linarith [hx.2]
    rw [(hasDerivAt_diagonalSplinePotential_four_outer ⟨hgt, hx2⟩).deriv,
      abs_of_nonneg (by positivity : 0 ≤ 3 / (2 - x))]
    apply (div_le_iff₀ (by linarith : 0 < 2 - x)).mpr
    linarith [hx.2]

theorem diagonalSplinePotential_four_cut : Spline.diagonalSplinePotential 4 1 = Real.log 6 := by
  unfold Spline.diagonalSplinePotential
  rw [diagonalSplineDensity_four_cut, one_div, Real.log_inv, neg_neg]

theorem four_potential_pos {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) (hxR : x < 2) :
    0 < Spline.diagonalSplinePotential 4 x := by
  have hxs : x ∈ Ioo (-Real.sqrt (4 : ℝ)) (Real.sqrt (4 : ℝ)) := by
    rw [sqrt_four_eq_two]
    constructor <;> linarith [hx.1]
  have hq0 := Spline.diagonalSplineDensity_pos 4 (by norm_num) x hxs
  have hq1 : Spline.diagonalSplineDensity 4 x < 1 := by
    by_cases hx1 : x ≤ 1
    · rw [diagonalSplineDensity_four_center ⟨hx.1, hx1⟩]
      have h := mul_nonneg (sq_nonneg x) (show 0 ≤ 2 - x by linarith)
      nlinarith
    · rw [diagonalSplineDensity_four_outer ⟨by linarith, hx.2⟩]
      have h := pow_le_pow_left₀ (show 0 ≤ 2 - x by linarith) (show 2 - x ≤ 1 by linarith) 3
      norm_num at h
      linarith
  exact neg_pos.mpr (Real.log_neg hq0 hq1)

theorem four_potential_near_zero_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 10)) :
    Spline.diagonalSplinePotential 4 x ≤ -Real.log ((3943 : ℝ) / 6000) := by
  have hq : (3943 : ℝ) / 6000 ≤ Spline.diagonalSplineDensity 4 x := by
    rw [diagonalSplineDensity_four_center ⟨hx.1, by linarith [hx.2]⟩]
    have hx2 : x ^ 2 ≤ x / 10 := by nlinarith [hx.1, hx.2]
    have hpos : 0 ≤ (1 / 10 - x) * (1 / 10 + x - ((1 / 10 : ℝ) ^ 2 + x / 10 + x ^ 2) / 2) :=
      mul_nonneg (by linarith [hx.2]) (by nlinarith [hx.1])
    nlinarith
  exact neg_le_neg (Real.log_le_log (by norm_num) hq)

end
end ENT.Small

/-! Radial integration by parts for genuine diagonal densities, with all endpoint
logarithms and derivative integrability justified. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Small

noncomputable section

theorem diagonal_entropy_eq_half_potential (n : ℕ) (hn : 2 ≤ n) :
    (Spline.diagonalFiniteEntropyDensity n hn).entropy =
      2 * ∫ x in 0..Real.sqrt (n : ℝ),
        Spline.diagonalSplineDensity n x * Spline.diagonalSplinePotential n x := by
  let f : ℝ → ℝ := fun x => Spline.diagonalSplineDensity n x *
    Real.log (Spline.diagonalSplineDensity n x)
  have hf : Continuous f :=
    Real.continuous_mul_log.comp (Spline.continuous_diagonalSplineDensity n)
  have hw : (∫ x, f x) = 2 * ∫ x in 0..Real.sqrt (n : ℝ), f x := by
    apply integral_even_of_bounded_support (Real.sqrt_nonneg _) hf
    · intro x
      simp only [f, Spline.diagonalSplineDensity_even n hn x]
    · intro x hx
      simp only [f, Spline.diagonalSplineDensity_eq_zero_of_not_mem n hn x hx, zero_mul]
  change -(∫ x, f x) = _
  rw [hw]
  have heq : (fun x => Spline.diagonalSplineDensity n x *
      Spline.diagonalSplinePotential n x) = fun x => -f x := by
    funext x
    simp only [Spline.diagonalSplinePotential, f, mul_neg]
  rw [heq, intervalIntegral.integral_neg]
  ring

theorem diagonal_half_mass (n : ℕ) (hn : 2 ≤ n) :
    (∫ x in 0..Real.sqrt (n : ℝ), Spline.diagonalSplineDensity n x) = (1 : ℝ) / 2 := by
  have h := integral_even_of_bounded_support (Real.sqrt_nonneg (n : ℝ))
    (Spline.continuous_diagonalSplineDensity n) (Spline.diagonalSplineDensity_even n hn)
    (Spline.diagonalSplineDensity_eq_zero_of_not_mem n hn)
  rw [Spline.integral_diagonalSplineDensity n hn] at h
  linarith

theorem diagonal_integral_mul_deriv (n : ℕ) (hn : 3 ≤ n) :
    (∫ x in 0..Real.sqrt (n : ℝ), x * deriv (Spline.diagonalSplineDensity n) x) = -(1 : ℝ) / 2 := by
  have hq := Spline.contDiff_diagonalSplineDensity 1 n (by omega)
  have hqd : Continuous (deriv (Spline.diagonalSplineDensity n)) := hq.continuous_deriv (by norm_num)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := (id : ℝ → ℝ)) (v := Spline.diagonalSplineDensity n)
    (u' := fun _ => (1 : ℝ)) (v' := deriv (Spline.diagonalSplineDensity n))
    (a := 0) (b := Real.sqrt (n : ℝ))
    continuous_id.continuousOn hq.continuous.continuousOn
    (fun x _ => hasDerivAt_id x)
    (fun x _ => (hq.differentiable (by norm_num) x).hasDerivAt)
    intervalIntegrable_const (hqd.intervalIntegrable _ _)
  simpa only [id_eq, Spline.diagonalSplineDensity_right_endpoint n (by omega), mul_zero,
    zero_mul, sub_zero, zero_sub, one_mul, diagonal_half_mass n (by omega), neg_div] using h

theorem diagonal_radial_integral (n : ℕ) (hn : 3 ≤ n) :
    (∫ x in 0..Real.sqrt (n : ℝ),
      (Spline.diagonalSplineDensity n x + x * deriv (Spline.diagonalSplineDensity n) x) *
        Spline.diagonalSplinePotential n x) = -(1 : ℝ) / 2 := by
  let q := Spline.diagonalSplineDensity n
  let V := Spline.diagonalSplinePotential n
  let A : ℝ → ℝ := fun x => -x * (q x * Real.log (q x))
  have hq : ContDiff ℝ 1 q := Spline.contDiff_diagonalSplineDensity 1 n (by omega)
  have hqd : Continuous (deriv q) := hq.continuous_deriv (by norm_num)
  have hA : Continuous A := (continuous_id.neg).mul (Real.continuous_mul_log.comp hq.continuous)
  have hR : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt (n : ℝ)),
      HasDerivAt A ((q x + x * deriv q x) * V x - x * deriv q x) x := by
    intro x hx
    have hqx : q x ≠ 0 := (Spline.diagonalSplineDensity_pos n (by omega) x
      ⟨by linarith [hx.1], hx.2⟩).ne'
    have hdq := (hq.differentiable (by norm_num) x).hasDerivAt
    have hdlog := (hdq.mul (hdq.log hqx))
    have h := (hasDerivAt_id x).neg.mul hdlog
    convert h using 1
    · rfl
    · dsimp [V, Spline.diagonalSplinePotential]
      field_simp
      ring
  have hV : IntervalIntegrable V volume 0 (Real.sqrt (n : ℝ)) :=
    (integrable_log_diagonalSplineDensity n (by omega)).neg.intervalIntegrable
  have hfirst : IntervalIntegrable (fun x => (q x + x * deriv q x) * V x)
      volume 0 (Real.sqrt (n : ℝ)) :=
    hV.continuousOn_mul (hq.continuous.add (continuous_id.mul hqd)).continuousOn
  have hsecond : IntervalIntegrable (fun x => x * deriv q x) volume 0 (Real.sqrt (n : ℝ)) :=
    (continuous_id.mul hqd).intervalIntegrable _ _
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR hA.continuousOn hderiv
    (hfirst.sub hsecond)
  have hAzero : A 0 = 0 := by simp [A]
  have hAright : A (Real.sqrt (n : ℝ)) = 0 := by
    simp only [A, q, Spline.diagonalSplineDensity_right_endpoint n (by omega), zero_mul, mul_zero]
  rw [hAzero, hAright, sub_zero, intervalIntegral.integral_sub hfirst hsecond] at hi
  have hrad := diagonal_integral_mul_deriv n hn
  change (∫ x in 0..Real.sqrt (n : ℝ), x * deriv q x) = -(1 : ℝ) / 2 at hrad
  change (∫ x in 0..Real.sqrt (n : ℝ), (q x + x * deriv q x) * V x) = _
  linarith

end
end ENT.Small

/-! Fourth-primitive kernel lemmas. -/
@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
attribute [local instance 1001] NormedField.toNormedSpace
namespace ENT.Small
noncomputable section
theorem boxPrimitive_four_eq_kernel {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {x : ℝ} (hx : 0 ≤ x)
    (hc : ContinuousOn f (Ioo 0 x)) :
    boxPrimitive f 4 x = (1 / 6) * ∫ t in 0..x, (x - t) ^ 3 * f t := by
  have hderiv : ∀ y ∈ Ioo (min 0 x) (max 0 x),
      HasDerivAt (boxPrimitive f 1) (f y) y := by
    intro y hy
    rw [min_eq_left hx, max_eq_right hx] at hy
    exact intervalIntegral.integral_hasDerivAt_right (hf 0 y)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hc y hy)
      ((hc y hy).continuousAt (isOpen_Ioo.mem_nhds hy))
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => (x - t) ^ 3) (v := boxPrimitive f 1)
    (u' := fun t => -3 * (x - t) ^ 2) (v' := f)
    (a := 0) (b := x)
    (by fun_prop) (continuous_boxPrimitive_succ hf 0).continuousOn
    (fun y _ => by
      convert ((hasDerivAt_const y x).sub (hasDerivAt_id y)).pow 3 using 1
      · rfl
      · simp only [Pi.sub_apply, id_eq]
        ring)
    hderiv ((show Continuous (fun t : ℝ => -3 * (x - t) ^ 2) by fun_prop).intervalIntegrable _ _) (hf 0 x)
  have hk := boxPrimitive_three_eq_kernel
    (fun a b => (continuous_boxPrimitive_succ hf 0).intervalIntegrable a b) hx
    (continuous_boxPrimitive_succ hf 0).continuousOn
  change boxPrimitive f 4 x = (1 / 2) * ∫ t in 0..x, (x - t) ^ 2 * boxPrimitive f 1 t at hk
  have hz : boxPrimitive f 1 0 = 0 := by simp
  simp only [sub_self, zero_pow (by decide : 3 ≠ 0), zero_mul, hz,
    mul_zero, sub_zero, zero_sub] at h
  have heq : (fun t : ℝ => (-3 * (x - t) ^ 2) * boxPrimitive f 1 t) =
      (fun t => -3 * ((x - t) ^ 2 * boxPrimitive f 1 t)) := by funext t; ring
  rw [heq, intervalIntegral.integral_const_mul] at h
  linarith

theorem boxPrimitive_four_le_of_bound {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {x M : ℝ} (hx : 0 ≤ x)
    (hc : ContinuousOn f (Ioo 0 x)) (hM : ∀ t ∈ Icc 0 x, f t ≤ M) :
    boxPrimitive f 4 x ≤ M * x ^ 4 / 24 := by
  rw [boxPrimitive_four_eq_kernel hf hx hc]
  have hfi : IntervalIntegrable (fun t => (x - t) ^ 3 * f t) volume 0 x :=
    (hf 0 x).continuousOn_mul (by fun_prop)
  have hgi : IntervalIntegrable (fun t : ℝ => (x - t) ^ 3 * M) volume 0 x :=
    (show Continuous (fun t : ℝ => (x - t) ^ 3 * M) by fun_prop).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono_on hx hfi hgi (fun t ht =>
    mul_le_mul_of_nonneg_left (hM t ht) (pow_nonneg (by linarith [ht.2]) 3))
  have heval : (∫ t in 0..x, (x - t) ^ 3 * M) = M * x ^ 4 / 4 := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_comp_sub_left (f := fun t : ℝ => t ^ 3), sub_self, sub_zero,
      integral_pow]
    norm_num
    ring
  rw [heval] at hi
  linarith

end
end ENT.Small

/-! The genuine fourth primitive and the jets used in the local n=4 argument. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace ENT.Small

noncomputable section

def fourPrimitive : ℝ → ℝ := boxPrimitive (Spline.diagonalSplinePotential 4) 4

theorem integrable_fourPotential : Integrable (Spline.diagonalSplinePotential 4) :=
  (integrable_log_diagonalSplineDensity 4 (by norm_num)).neg

theorem fourPrimitive_even : Function.Even fourPrimitive := by
  intro x
  simpa only [fourPrimitive, pow_succ, pow_zero, neg_mul, one_mul, mul_one, neg_neg]
    using boxPrimitive_parity (Spline.diagonalSplinePotential_even 4 (by norm_num)) 4 x

theorem contDiff_fourPrimitive_three : ContDiff ℝ 3 fourPrimitive :=
  contDiff_boxPrimitive_succ (fun _ _ => integrable_fourPotential.intervalIntegrable) 3

theorem contDiffOn_fourPrimitive_five :
    ContDiffOn ℝ 5 fourPrimitive (Ioo (-2 : ℝ) 2) := by
  exact contDiffOn_boxPrimitive (fun _ _ => integrable_fourPotential.intervalIntegrable)
    isOpen_Ioo 1 4 (contDiffOn_diagonalSplinePotential_four 1 (by norm_num))

theorem deriv_fourPrimitive :
    deriv fourPrimitive = boxPrimitive (Spline.diagonalSplinePotential 4) 3 :=
  deriv_boxPrimitive_succ_succ (fun _ _ => integrable_fourPotential.intervalIntegrable) 2

theorem second_deriv_fourPrimitive :
    iteratedDeriv 2 fourPrimitive = boxPrimitive (Spline.diagonalSplinePotential 4) 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_fourPrimitive]
  exact deriv_boxPrimitive_succ_succ (fun _ _ => integrable_fourPotential.intervalIntegrable) 1

theorem third_deriv_fourPrimitive :
    iteratedDeriv 3 fourPrimitive = boxPrimitive (Spline.diagonalSplinePotential 4) 1 := by
  rw [iteratedDeriv_succ, second_deriv_fourPrimitive]
  exact deriv_boxPrimitive_succ_succ (fun _ _ => integrable_fourPotential.intervalIntegrable) 0

theorem fourth_deriv_fourPrimitive {x : ℝ} (hx : x ∈ Ioo (-2 : ℝ) 2) :
    iteratedDeriv 4 fourPrimitive x = Spline.diagonalSplinePotential 4 x := by
  rw [iteratedDeriv_succ, third_deriv_fourPrimitive]
  have hc := (contDiffOn_diagonalSplinePotential_four 1 (by norm_num)).continuousOn
  exact (hasDerivAt_intervalPrimitive (fun _ _ => integrable_fourPotential.intervalIntegrable)
    ((hc x hx).continuousAt (isOpen_Ioo.mem_nhds hx))
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hc x hx)).deriv

theorem fifth_deriv_fourPrimitive {x : ℝ} (hx : x ∈ Ioo (-2 : ℝ) 2) :
    iteratedDeriv 5 fourPrimitive x = deriv (Spline.diagonalSplinePotential 4) x := by
  have heq : iteratedDeriv 4 fourPrimitive =ᶠ[𝓝 x] Spline.diagonalSplinePotential 4 := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact fourth_deriv_fourPrimitive hy
  rw [iteratedDeriv_succ]
  exact heq.deriv_eq

theorem fourPrimitive_second_one : iteratedDeriv 2 fourPrimitive 1 = fourJ2 := by
  rw [second_deriv_fourPrimitive]
  exact boxPrimitive_two_eq_kernel (fun _ _ => integrable_fourPotential.intervalIntegrable)
    (by norm_num) ((contDiffOn_diagonalSplinePotential_four 1 (by norm_num)).continuousOn.mono
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))

theorem fourPrimitive_third_one : iteratedDeriv 3 fourPrimitive 1 = fourJ3 := by
  rw [third_deriv_fourPrimitive]
  rfl

theorem fourPrimitive_fourth_one : iteratedDeriv 4 fourPrimitive 1 = fourV := by
  rw [fourth_deriv_fourPrimitive (by constructor <;> norm_num),
    diagonalSplinePotential_four_cut]
  rfl

theorem four_expectation_primitive (a : Fin 4 → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ x, Spline.diagonalSplinePotential 4 x ∂projectionLaw a) =
      fourBoxNumerator fourPrimitive (a 0) (a 1) (a 2) (a 3) /
        (8 * a 0 * a 1 * a 2 * a 3) :=
  integral_projection_four_primitive a ha integrable_fourPotential
    (Spline.diagonalSplinePotential_even 4 (by norm_num))

theorem four_diagonal_potential_expectation :
    (∫ x, Spline.diagonalSplinePotential 4 x ∂projectionLaw (diagonal 4)) = fourH := by
  let p := Spline.diagonalFiniteEntropyDensity 4 (by norm_num)
  calc
    _ = ∫ x, (-Real.log (p.density x)) * p.density x := p.integral_eq_density _
    _ = p.entropy := by
      unfold FiniteEntropyDensity.entropy
      rw [← integral_neg]
      congr 1
      funext x
      ring
    _ = fourH := rfl

theorem fourPrimitive_diagonal_identity :
    fourPrimitive 2 - 4 * fourPrimitive 1 = fourH / 2 := by
  have hd : ∀ i : Fin 4, diagonal 4 i = (1 : ℝ) / 2 := by
    intro i
    simp only [diagonal, Nat.cast_ofNat, sqrt_four_eq_two]
    norm_num
  have h := four_expectation_primitive (diagonal 4) (by intro i; rw [hd]; norm_num)
  rw [four_diagonal_potential_expectation] at h
  have hz : fourPrimitive 0 = 0 := by simp [fourPrimitive]
  simp only [hd, fourBoxNumerator] at h
  norm_num at h
  rw [hz] at h
  linarith

theorem four_potential_outer_weighted_integral :
    (∫ x in (1 : ℝ)..2, (2 - x) * Spline.diagonalSplinePotential 4 x) =
      fourV / 2 + 3 / 4 := by
  have hi : IntervalIntegrable (fun x : ℝ => x * Real.log x) volume 0 1 :=
    Real.continuous_mul_log.intervalIntegrable _ _
  have hlog : (∫ x in (0 : ℝ)..1, x * Real.log x) = -(1 : ℝ) / 4 := by
    rw [integral_mul_log_from_zero (by norm_num)]
    norm_num
  calc
    _ = ∫ x in (1 : ℝ)..2, (2 - x) * (-Real.log ((2 - x) ^ 3 / 6)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
      simp only [Spline.diagonalSplinePotential, diagonalSplineDensity_four_outer hx]
    _ = ∫ x in (0 : ℝ)..1, x * (-Real.log (x ^ 3 / 6)) := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ => x * (-Real.log (x ^ 3 / 6))) (a := 1) (b := 2) 2
      simpa only [sub_self, show (2 : ℝ) - 1 = 1 by norm_num] using h
    _ = ∫ x in (0 : ℝ)..1, fourV * x - 3 * (x * Real.log x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      by_cases hx0 : x = 0
      · simp [hx0]
      · rw [Real.log_div (pow_ne_zero 3 hx0) (by norm_num : (6 : ℝ) ≠ 0), Real.log_pow]
        unfold fourV
        ring
    _ = _ := by
      rw [intervalIntegral.integral_sub
        ((show Continuous (fun x : ℝ => fourV * x) by fun_prop).intervalIntegrable 0 1) (hi.const_mul 3),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        hlog, integral_id]
      norm_num
      ring

theorem fourPrimitive_second_right : iteratedDeriv 2 fourPrimitive 2 = fourF2R := by
  have h := boxPrimitive_two_difference
    (fun _ _ => integrable_fourPotential.intervalIntegrable)
    (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 2 by norm_num)
    ((contDiffOn_diagonalSplinePotential_four 1 (by norm_num)).continuousOn.mono
      (fun x hx => ⟨by linarith [hx.1], hx.2⟩))
  change boxPrimitive (Spline.diagonalSplinePotential 4) 2 2 -
    boxPrimitive (Spline.diagonalSplinePotential 4) 2 1 =
      (2 - 1) * fourJ3 + _ at h
  rw [four_potential_outer_weighted_integral] at h
  rw [second_deriv_fourPrimitive]
  have hj := fourPrimitive_second_one
  rw [second_deriv_fourPrimitive] at hj
  unfold fourF2R
  linarith

theorem fourPrimitive_small_bound {x : ℝ} (hx : |x| ≤ (1 : ℝ) / 10) :
    fourPrimitive x ≤ (421 : ℝ) * x ^ 4 / 24000 := by
  have hbound : fourPrimitive |x| ≤ ((421 : ℝ) / 1000) * |x| ^ 4 / 24 := by
    apply boxPrimitive_four_le_of_bound (fun _ _ => integrable_fourPotential.intervalIntegrable)
      (abs_nonneg x)
    · exact (contDiffOn_diagonalSplinePotential_four 1 (by norm_num)).continuousOn.mono
        (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    · intro y hy
      exact (four_potential_near_zero_le ⟨hy.1, le_trans hy.2 hx⟩).trans
        four_potential_one_tenth_bound
  have heq : fourPrimitive |x| = fourPrimitive x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, fourPrimitive_even x]
  have habs : |x| ^ 4 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, sq_abs]
    ring
  rw [heq, habs] at hbound
  convert hbound using 1 <;> ring

end
end ENT.Small

/-! The radial first-jet identity of the genuine fourth primitive. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Small
noncomputable section

theorem fourPrimitive_radial_identity :
    4 * fourH + 8 * deriv fourPrimitive 1 - 4 * deriv fourPrimitive 2 = -1 := by
  let q := Spline.diagonalSplineDensity 4
  let V := Spline.diagonalSplinePotential 4
  let w : ℝ → ℝ := fun x => q x + x * deriv q x
  have hv (a b : ℝ) : IntervalIntegrable V volume a b :=
    integrable_fourPotential.intervalIntegrable
  have hweight (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) :
      IntervalIntegrable (fun x => g x * V x) volume a b :=
    (hv a b).continuousOn_mul hg.continuousOn
  have hq : ContDiff ℝ 1 q := Spline.contDiff_diagonalSplineDensity 1 4 (by norm_num)
  have hw : Continuous w := hq.continuous.add (continuous_id.mul (hq.continuous_deriv (by norm_num)))
  have hqV (a b : ℝ) := hweight q hq.continuous a b
  have hwV (a b : ℝ) := hweight w hw a b
  have hK (a b c : ℝ) := hweight (fun x : ℝ => (c - x) ^ 2) (by fun_prop) a b
  have hL (a b : ℝ) := hweight (fun x : ℝ => 1 - x ^ 2 / 2) (by fun_prop) a b
  have hc : ContinuousOn V (Ioo (0 : ℝ) 2) :=
    (contDiffOn_diagonalSplinePotential_four 1 (by norm_num)).continuousOn.mono
      (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have hk2 := boxPrimitive_three_eq_kernel hv (show (0 : ℝ) ≤ 2 by norm_num) hc
  have hk1 := boxPrimitive_three_eq_kernel hv (show (0 : ℝ) ≤ 1 by norm_num)
    (hc.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hK 0 1 2) (hK 1 2 2)
  have hcenter : (∫ x in (0 : ℝ)..1, (1 - x ^ 2 / 2) * V x) =
      (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..1, (2 - x) ^ 2 * V x) -
        ∫ x in (0 : ℝ)..1, (1 - x) ^ 2 * V x := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hK 0 1 2).const_mul _) (hK 0 1 1)]
    congr 1
    funext x
    ring
  have hprimitive : deriv fourPrimitive 2 - 2 * deriv fourPrimitive 1 =
      (∫ x in (0 : ℝ)..1, (1 - x ^ 2 / 2) * V x) +
        (1 / 2 : ℝ) * ∫ x in (1 : ℝ)..2, (2 - x) ^ 2 * V x := by
    rw [deriv_fourPrimitive]
    change boxPrimitive V 3 2 - 2 * boxPrimitive V 3 1 = _
    linarith only [hk2, hk1, hsplit, hcenter]
  have hcidentity : (∫ x in (0 : ℝ)..1, (1 - x ^ 2 / 2) * V x) =
      2 * (∫ x in (0 : ℝ)..1, q x * V x) -
        (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, w x * V x := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hqV 0 1).const_mul _) ((hwV 0 1).const_mul _)]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp only [w, q]
    rw [diagonalSplineDensity_four_center ⟨hx.1.le, hx.2.le⟩,
      (hasDerivAt_diagonalSplineDensity_four_center hx).deriv]
    ring
  have hoidentity : (1 / 2 : ℝ) * (∫ x in (1 : ℝ)..2, (2 - x) ^ 2 * V x) =
      2 * (∫ x in (1 : ℝ)..2, q x * V x) -
        (1 / 2 : ℝ) * ∫ x in (1 : ℝ)..2, w x * V x := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hqV 1 2).const_mul _) ((hwV 1 2).const_mul _)]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp only [w, q]
    rw [diagonalSplineDensity_four_outer ⟨hx.1.le, hx.2.le⟩,
      (hasDerivAt_diagonalSplineDensity_four_outer hx).deriv]
    ring
  have hentropy := diagonal_entropy_eq_half_potential 4 (by norm_num)
  simp only [Nat.cast_ofNat, sqrt_four_eq_two] at hentropy
  change fourH = 2 * ∫ x in (0 : ℝ)..2, q x * V x at hentropy
  have hradial := diagonal_radial_integral 4 (by norm_num)
  simp only [Nat.cast_ofNat, sqrt_four_eq_two] at hradial
  change (∫ x in (0 : ℝ)..2, w x * V x) = -(1 : ℝ) / 2 at hradial
  have hqsplit := intervalIntegral.integral_add_adjacent_intervals (hqV 0 1) (hqV 1 2)
  have hwsplit := intervalIntegral.integral_add_adjacent_intervals (hwV 0 1) (hwV 1 2)
  linarith only [hprimitive, hcidentity, hoidentity, hentropy, hradial, hqsplit, hwsplit]

end
end ENT.Small

/-! Analytic Taylor bounds for the actual fourth primitive. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology

namespace ENT.Small
noncomputable section

def fourInnerTaylor (x : ℝ) : ℝ :=
  fourPrimitive 1 + deriv fourPrimitive 1 * (x - 1) +
    fourJ2 * (x - 1) ^ 2 / 2 + fourJ3 * (x - 1) ^ 3 / 6 +
      fourV * (x - 1) ^ 4 / 24

theorem fourInnerTaylor_eq_taylorFour (x : ℝ) :
    fourInnerTaylor x = taylorFour fourPrimitive 1 x := by
  unfold fourInnerTaylor taylorFour
  rw [fourPrimitive_second_one, fourPrimitive_third_one, fourPrimitive_fourth_one]

theorem fourPrimitive_inner_remainder {x : ℝ} (hx : x ∈ Icc ((3 : ℝ) / 4) (5 / 4)) :
    |fourPrimitive x - fourInnerTaylor x| ≤ |x - 1| ^ 5 / 30 := by
  have hmin : (3 : ℝ) / 4 ≤ min 1 x := le_min (by norm_num) hx.1
  have hmax : max 1 x ≤ (5 : ℝ) / 4 := max_le (by norm_num) hx.2
  have hsub : uIcc 1 x ⊆ Ioo (-2 : ℝ) 2 := by
    intro y hy
    change min 1 x ≤ y ∧ y ≤ max 1 x at hy
    constructor <;> linarith [hy.1, hy.2]
  have hderiv : ∀ y ∈ uIoo 1 x, ∃ v : ℝ,
      HasDerivAt (iteratedDeriv 4 fourPrimitive) v y ∧ |v| ≤ 4 := by
    intro y hy
    have hys : y ∈ Ioo (-2 : ℝ) 2 := hsub ⟨hy.1.le, hy.2.le⟩
    have heq : iteratedDeriv 4 fourPrimitive =ᶠ[𝓝 y] Spline.diagonalSplinePotential 4 := by
      filter_upwards [Ioo_mem_nhds hys.1 hys.2] with z hz
      exact fourth_deriv_fourPrimitive hz
    have hd := ((contDiffOn_diagonalSplinePotential_four 1 (by norm_num) y hys).contDiffAt
      (isOpen_Ioo.mem_nhds hys)).differentiableAt (by norm_num)
    exact ⟨_, hd.hasDerivAt.congr_of_eventuallyEq heq,
      abs_deriv_diagonalSplinePotential_four_le
        ⟨le_trans hmin hy.1.le, le_trans hy.2.le hmax⟩⟩
  have h := taylorFour_remainder_bound isOpen_Ioo
    (contDiffOn_fourPrimitive_five.of_le (by norm_num)) hsub hderiv
  rw [← fourInnerTaylor_eq_taylorFour] at h
  convert h using 1 <;> ring

theorem fourPrimitive_inner_lower {x : ℝ} (hx : x ∈ Icc ((3 : ℝ) / 4) (5 / 4)) :
    fourInnerTaylor x - |x - 1| ^ 5 / 30 ≤ fourPrimitive x := by
  have h := (abs_le.mp (fourPrimitive_inner_remainder hx)).1
  linarith

theorem fourPrimitive_outer_upper {A : ℝ} (hA0 : 0 < A) (hA2 : A ≤ 2) :
    fourPrimitive A ≤ fourPrimitive 2 + deriv fourPrimitive 2 * (A - 2) +
      fourF2R * (A - 2) ^ 2 / 2 := by
  rw [← fourPrimitive_second_right]
  apply taylorSecond_upper_of_nonneg_third
    (contDiff_fourPrimitive_three.of_le (by norm_num)) hA2
  intro y hy
  have hy0 : 0 < y := lt_trans hA0 hy.1
  refine ⟨boxPrimitive (Spline.diagonalSplinePotential 4) 1 y, ?_, ?_⟩
  · rw [second_deriv_fourPrimitive]
    exact hasDerivAt_boxPrimitive_succ_succ
      (fun _ _ => integrable_fourPotential.intervalIntegrable) 0 y
  · change 0 ≤ ∫ x in 0..y, Spline.diagonalSplinePotential 4 x
    apply intervalIntegral.integral_nonneg hy0.le
    intro x hx
    exact (four_potential_pos ⟨hx.1, le_trans hx.2 hy.2.le⟩
      (lt_of_le_of_lt hx.2 hy.2)).le

end
end ENT.Small
