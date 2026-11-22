module

public import ENT.Small.HessianIntegration
public import ENT.Small.EnvelopeTransport

/-! The actual cube Hessian expectation, including its integrability.
Rational derivative expressions are used only as measurable representatives;
they are proved equal to the genuine potential derivative almost everywhere. -/

@[expose] public section
attribute [local instance 1001] NormedField.toNormedSpace
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ENT.Small
noncomputable section
open Spline

theorem measurable_logSecondRatio (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) :
    Measurable (logSecondRatio f) := by
  have hdd : Continuous (deriv (deriv f)) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hf.continuous_iteratedDeriv' 2
  exact (hdd.measurable.div hf.continuous.measurable).sub
    (((hf.continuous_deriv (by norm_num)).measurable.div hf.continuous.measurable).pow_const 2)

def diagonalHessian (n : ℕ) (x : ℝ) : ℝ :=
  -(n:ℝ)/4*logSecondRatio (unitSumSplineDensity n) (((n:ℝ)-Real.sqrt (n:ℝ)*x)/2)

theorem measurable_diagonalHessian (n : ℕ) (hn : 4≤n) : Measurable (diagonalHessian n) :=
  ((measurable_logSecondRatio _ (contDiff_unitSumSplineDensity 2 n (by omega))).comp
    (by fun_prop)).const_mul _

theorem diagonalHessian_sumToDiagonal (n : ℕ) (hn : 0<n) (t : ℝ) :
    diagonalHessian n (sumToDiagonal n t)=-(n:ℝ)/4*logSecondRatio (unitSumSplineDensity n) t := by
  rw [diagonalHessian,sumToDiagonal_inverse_coordinate n hn]

theorem diagonalHessian_eq_second (n : ℕ) (hn : 4≤n) {x : ℝ}
    (hx : x∈Ioo (-Real.sqrt (n:ℝ)) (Real.sqrt (n:ℝ))) :
    diagonalHessian n x=deriv (deriv (diagonalSplinePotential n)) x := by
  have h := diagonalPotential_iteratedDeriv n (by omega) 2 (by decide) hx
  have hq := diagonalSplineDensity_pos n (by omega) x hx
  have hfn : unitSumSplineDensity n (((n:ℝ)-Real.sqrt (n:ℝ)*x)/2)≠0 := by
    intro hz
    unfold diagonalSplineDensity at hq
    rw [hz,mul_zero] at hq
    exact (lt_irrefl 0) hq
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at h
  rw [second_deriv_log_eq_ratio _ (contDiff_unitSumSplineDensity 2 n (by omega)) _ hfn,
    div_pow,neg_sq,Real.sq_sqrt (Nat.cast_nonneg n)] at h
  rw [h]
  unfold diagonalHessian
  ring

def outerDensityLogSecond (n : ℕ) (x : ℝ) : ℝ := if n=5 then -x^2/6 else -x^3/24

theorem continuous_outerDensityLogSecond (n : ℕ) : Continuous (outerDensityLogSecond n) := by
  unfold outerDensityLogSecond
  split_ifs <;> fun_prop

theorem density_logSecond_outer (n : ℕ) (hn : n=5 ∨ n=6) (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    unitSumSplineDensity n x*logSecondRatio (unitSumSplineDensity n) x=outerDensityLogSecond n x := by
  rcases hn with rfl | rfl
  · obtain ⟨hf,hf1,hf2⟩ := unit_density_five_outer_jets x hx
    rw [logSecondRatio,hf,hf1,hf2]
    simp only [outerDensityLogSecond,ite_true]
    by_cases h0 : x=0
    · simp [h0]
    · field_simp
      ring
  · obtain ⟨hf,hf1,hf2⟩ := unit_density_six_outer_jets x hx
    rw [logSecondRatio,hf,hf1,hf2]
    norm_num only [outerDensityLogSecond,ite_false]
    by_cases h0 : x=0
    · simp [h0]
    · field_simp
      ring

theorem continuousOn_density_logSecond_five_six (n : ℕ) (hn : n=5 ∨ n=6) :
    ContinuousOn (fun x=>unitSumSplineDensity n x*logSecondRatio (unitSumSplineDensity n) x)
      (Icc (0:ℝ) n) := by
  have hfn := contDiff_unitSumSplineDensity 2 n (by omega)
  have hsym (x : ℝ) :
      unitSumSplineDensity n ((n:ℝ)-x)*logSecondRatio (unitSumSplineDensity n) ((n:ℝ)-x)=
        unitSumSplineDensity n x*logSecondRatio (unitSumSplineDensity n) x := by
    rw [unitSumSplineDensity_reflection n (by omega),
      logSecondRatio_reflection _ n hfn (unitSumSplineDensity_reflection n (by omega))]
  apply continuousOn_from_endpoint_formulas _ (outerDensityLogSecond n)
    (fun x=>outerDensityLogSecond n ((n:ℝ)-x)) n (by exact_mod_cast (by omega : 1<n))
    (continuous_outerDensityLogSecond n)
    ((continuous_outerDensityLogSecond n).comp (continuous_const.sub continuous_id))
    (density_logSecond_outer n hn)
  · intro x hx
    rw [←hsym x]
    exact density_logSecond_outer n hn _ ⟨by linarith [hx.2],by linarith [hx.1]⟩
  · intro x hx
    exact hfn.continuous.continuousAt.mul (continuousAt_logSecondRatio _ hfn x
      (unitSumSplineDensity_pos n (by omega) x hx.1 hx.2).ne')

theorem integrable_density_logSecond_five_six (n : ℕ) (hn : n=5 ∨ n=6) :
    Integrable (fun x=>unitSumSplineDensity n x*logSecondRatio (unitSumSplineDensity n) x) volume := by
  apply (continuousOn_density_logSecond_five_six n hn).integrableOn_Icc.integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [unitSumSplineDensity_eq_zero_of_not_mem n (by omega) x hx,zero_mul]

theorem integrable_diagonalHessian_cube (n : ℕ) (hn : n=5 ∨ n=6) :
    Integrable (fun x=>diagonalHessian n (projection (diagonal n) x)) (cubeLaw n) := by
  apply (integrable_diagonal_iff_sum_coordinate n (by omega) (diagonalHessian n)
    (measurable_diagonalHessian n (by omega))).mpr
  have h := (integrable_density_logSecond_five_six n hn).const_mul (-(n:ℝ)/4)
  apply h.congr
  exact Filter.Eventually.of_forall fun t=>by
    dsimp only
    rw [diagonalHessian_sumToDiagonal n (by omega)]
    ring

theorem diagonalHessian_ae_eq_second_cube (n : ℕ) (hn : 4≤n) :
    (fun x=>diagonalHessian n (projection (diagonal n) x))=ᶠ[ae (cubeLaw n)]
      (fun x=>deriv (deriv (diagonalSplinePotential n)) (projection (diagonal n) x)) := by
  have h := ae_of_ae_map (measurable_projection (diagonal n)).aemeasurable
    (ae_mem_diagonalSplineSupport n (by omega))
  filter_upwards [h] with x hx
  exact diagonalHessian_eq_second n hn hx

theorem integrable_diagonalPotential_second_cube (n : ℕ) (hn : n=5 ∨ n=6) :
    Integrable (fun x=>deriv (deriv (diagonalSplinePotential n)) (projection (diagonal n) x))
      (cubeLaw n) :=
  (integrable_diagonalHessian_cube n hn).congr (diagonalHessian_ae_eq_second_cube n (by omega))

theorem weighted_logSecond_integral_full (n : ℕ) (hn : n=5 ∨ n=6) :
    (∫ t,varianceKernel n t*logSecondRatio (unitSumSplineDensity n) t)=
      ∫ t in (0:ℝ)..n,varianceKernel n t*logSecondRatio (unitSumSplineDensity n) t := by
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n),←integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro t ht
  rw [varianceKernel_eq_zero_of_not_mem n (by omega) t ht,zero_mul]

theorem hessian_expectation_five_six {n : ℕ} (hn : n=5 ∨ n=6)
    (b : Fin n → ℝ) (hb : ∑ i,b i=0) :
    Integrable (fun x=>projection b x^2*deriv (deriv (diagonalSplinePotential n))
      (projection (diagonal n) x)) (cubeLaw n) ∧
      (∫ x,projection b x^2*deriv (deriv (diagonalSplinePotential n))
        (projection (diagonal n) x) ∂cubeLaw n)=(1-smallKappa n)*perturbationEnergy b := by
  have hi := integrable_diagonalHessian_cube n hn
  have heq := diagonalHessian_ae_eq_second_cube n (by omega)
  have hweighted : (fun x=>projection b x^2*diagonalHessian n (projection (diagonal n) x))=ᶠ[ae (cubeLaw n)]
      (fun x=>projection b x^2*deriv (deriv (diagonalSplinePotential n)) (projection (diagonal n) x)) :=
    heq.mono fun x hx=>by
      dsimp only at hx ⊢
      rw [hx]
  refine ⟨(integrable_projection_sq_diagonal_test b hi).congr hweighted,?_⟩
  rw [←integral_congr_ae hweighted,
    integral_zero_sum_projection_sq_eq_varianceKernel (by omega) b hb (diagonalHessian n)
      (measurable_diagonalHessian n (by omega)) hi]
  have hfun : (fun t=>varianceKernel n t*diagonalHessian n (sumToDiagonal n t))=
      (fun t=>(-(n:ℝ)/4)*(varianceKernel n t*logSecondRatio (unitSumSplineDensity n) t)) := by
    funext t
    rw [diagonalHessian_sumToDiagonal n (by omega)]
    ring
  rw [hfun,integral_const_mul,weighted_logSecond_integral_full n hn]
  have h := congrArg (fun x : ℝ=>perturbationEnergy b*x) (hessian_kernel_integral_five_six n hn)
  nlinarith only [h]

end
end ENT.Small
