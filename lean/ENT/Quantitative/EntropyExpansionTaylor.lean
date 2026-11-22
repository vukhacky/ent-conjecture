module

public import ENT.Quantitative.EdgeworthPolynomials
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Global cubic expansion of the Gibbs integrand with a quartic remainder.
The estimate is valid all the way to zero density; no small relative-error
hypothesis and no undefined logarithm is used. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
namespace ENT.Quantitative
noncomputable section

private theorem nonneg_of_deriv_sign {F G : ℝ→ℝ}
    (hder : ∀y,0<y→HasDerivAt F (G y) y)
    (hleft : ∀y,0<y→y≤1→G y≤0)
    (hright : ∀y,1≤y→0≤G y)
    (hzero : F 1=0) {y : ℝ} (hy : 0<y) : 0≤F y := by
  by_cases hy1 : y≤1
  · have hm : AntitoneOn F (Icc y 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact fun z hz=>(hder z (hy.trans_le hz.1)).continuousAt.continuousWithinAt
      · exact fun z hz=>(hder z (hy.trans_le (interior_subset hz).1)).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [(hder z (hy.trans_le (interior_subset hz).1)).deriv]
        exact hleft z (hy.trans_le (interior_subset hz).1) (interior_subset hz).2
    simpa only [hzero] using hm ⟨le_rfl,hy1⟩ ⟨hy1,le_rfl⟩ hy1
  · have hy1 : 1≤y := le_of_lt (lt_of_not_ge hy1)
    have hm : MonotoneOn F (Icc 1 y) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun z hz=>(hder z (lt_of_lt_of_le (by norm_num) hz.1)).continuousAt.continuousWithinAt
      · exact fun z hz=>(hder z (lt_of_lt_of_le (by norm_num) (interior_subset hz).1)).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [(hder z (lt_of_lt_of_le (by norm_num) (interior_subset hz).1)).deriv]
        exact hright z (interior_subset hz).1
    simpa only [hzero] using hm ⟨le_rfl,hy1⟩ ⟨hy1,le_rfl⟩ hy1

private def entropyCubicRemainder (y : ℝ) : ℝ :=
  y*Real.log y-(y-1)-(y-1)^2/2+(y-1)^3/6

private theorem entropyCubicRemainder_nonneg {y : ℝ} (hy : 0<y) :
    0≤entropyCubicRemainder y := by
  let G : ℝ→ℝ := fun z=>Real.log z+z^2/2-2*z+3/2
  have hG (z : ℝ) (hz : 0<z) : HasDerivAt G ((z-1)^2/z) z := by
    dsimp [G]
    convert (((Real.hasDerivAt_log hz.ne').add (((hasDerivAt_id z).pow 2).div_const 2)).sub
      ((hasDerivAt_id z).const_mul 2)).add_const (3/2) using 1
    · rfl
    · simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,id_eq]
      field_simp
      ring
  have hm : MonotoneOn G (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
    · exact fun z hz=>(hG z hz).continuousAt.continuousWithinAt
    · exact fun z hz=>(hG z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hG z (interior_subset hz)).deriv]
      exact div_nonneg (sq_nonneg _) (interior_subset hz).le
  have hG1 : G 1=0 := by norm_num [G]
  apply nonneg_of_deriv_sign (G:=G) _ _ _ _ hy
  · intro z hz
    unfold entropyCubicRemainder
    convert ((((hasDerivAt_id z).mul (Real.hasDerivAt_log hz.ne')).sub
      ((hasDerivAt_id z).sub_const 1)).sub
      ((((hasDerivAt_id z).sub_const 1).pow 2).div_const 2)).add
      ((((hasDerivAt_id z).sub_const 1).pow 3).div_const 6) using 1
    · rfl
    · dsimp [G]
      simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,id_eq]
      field_simp
      ring
  · intro z hz hz1
    simpa only [hG1] using hm hz (by norm_num) hz1
  · intro z hz1
    simpa only [hG1] using hm (by norm_num) (lt_of_lt_of_le (by norm_num) hz1) hz1
  · norm_num [entropyCubicRemainder]

private theorem log_cubic_upper {y : ℝ} (hy : 0<y) :
    Real.log y≤(y-1)-(y-1)^2/2+(y-1)^3/3 := by
  let F : ℝ→ℝ := fun z=>(z-1)-(z-1)^2/2+(z-1)^3/3-Real.log z
  have hder (z : ℝ) (hz : 0<z) : HasDerivAt F ((z-1)^3/z) z := by
    dsimp [F]
    convert ((((hasDerivAt_id z).sub_const 1).sub
      ((((hasDerivAt_id z).sub_const 1).pow 2).div_const 2)).add
      ((((hasDerivAt_id z).sub_const 1).pow 3).div_const 3)).sub
      (Real.hasDerivAt_log hz.ne') using 1
    · rfl
    · simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,id_eq]
      field_simp
      ring
  have h := nonneg_of_deriv_sign hder (by
    intro z hz hz1
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (z-1)]) hz.le)
    (by intro z hz; positivity)
    (by norm_num [F]) hy
  dsimp [F] at h
  linarith

/-- A global fourth-order error bound for the entropy integrand. -/
theorem entropy_cubic_taylor_bounds {y : ℝ} (hy : 0≤y) :
    0≤y*Real.log y-(y-1)-(y-1)^2/2+(y-1)^3/6 ∧
    y*Real.log y-(y-1)-(y-1)^2/2+(y-1)^3/6≤(y-1)^4/3 := by
  obtain rfl|hy := eq_or_lt_of_le hy
  · norm_num
  · refine ⟨entropyCubicRemainder_nonneg hy,?_⟩
    have h := mul_le_mul_of_nonneg_left (log_cubic_upper hy) hy.le
    nlinarith

theorem gibbsDefect_eq_relative {u v : ℝ} (hv : 0<v) :
    gibbsDefect u v=v*((u/v)*Real.log (u/v)-(u/v-1)) := by
  by_cases hu : u=0
  · simp [hu,gibbsDefect]
  · rw [gibbsDefect,Real.log_div hu hv.ne']
    field_simp
    ring

/-- Absolute polynomial approximation in the density difference, valid for
all nonnegative densities and every strictly positive reference density. -/
theorem gibbsDefect_cubic_error {u v : ℝ} (hu : 0≤u) (hv : 0<v) :
    |gibbsDefect u v-((u-v)^2/(2*v)-(u-v)^3/(6*v^2))|≤(u-v)^4/(3*v^3) := by
  have h := entropy_cubic_taylor_bounds (div_nonneg hu hv.le)
  have he : gibbsDefect u v-((u-v)^2/(2*v)-(u-v)^3/(6*v^2))=
      v*((u/v)*Real.log (u/v)-(u/v-1)-(u/v-1)^2/2+(u/v-1)^3/6) := by
    rw [gibbsDefect_eq_relative hv]
    field_simp
    ring
  rw [he,abs_of_nonneg (mul_nonneg hv.le h.1)]
  have hh := mul_le_mul_of_nonneg_left h.2 hv.le
  convert hh using 1
  field_simp <;> ring

end
end ENT.Quantitative
