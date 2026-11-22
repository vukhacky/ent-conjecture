module

public import ENT.Quantitative.EntropyExpansionTaylor
public import ENT.Quantitative.PangGaussianEnvelope
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Gaussian polynomial envelopes and the expanding central region used for
entropy integration. The region is written exponentially, avoiding any use
of totalized logarithms at dimension zero. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory Polynomial Filter
open scoped Topology
namespace ENT.Quantitative
noncomputable section

def entropyCentralSet (n : ℕ) : Set ℝ := {x | Real.exp (x^2/7)≤(n:ℝ)}

theorem measurableSet_entropyCentralSet (n : ℕ) : MeasurableSet (entropyCentralSet n) :=
  measurableSet_le (by fun_prop) measurable_const

theorem eventually_mem_entropyCentralSet (x : ℝ) : ∀ᶠn : ℕ in atTop, x∈entropyCentralSet n :=
  tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp (x^2/7)))

theorem integrable_polynomial_gaussian {b : ℝ} (hb : 0<b) (p : ℝ[X]) :
    Integrable (fun x : ℝ=>p.eval (x^2)*Real.exp (-b*x^2)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add,add_mul] using hp.fun_add hq
  | monomial k c =>
    have h := integrable_rpow_mul_exp_neg_mul_sq hb
      (show (-1:ℝ)<(2*k:ℕ) by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
    simp only [Real.rpow_natCast] at h
    simpa only [eval_monomial,←pow_mul,mul_assoc] using h.const_mul c

theorem integrable_abs_polynomial_gaussian {b : ℝ} (hb : 0<b) (p : ℝ[X]) :
    Integrable (fun x : ℝ=>|p.eval (x^2)| *Real.exp (-b*x^2)) := by
  simpa only [abs_mul,abs_of_pos (Real.exp_pos _)] using (integrable_polynomial_gaussian hb p).abs

theorem abs_mul_log_le_rpow_add_sq {z : ℝ} (hz : 0≤z) :
    |z*Real.log z|≤64*z^(63/64:ℝ)+z^2 := by
  obtain rfl|hz := eq_or_lt_of_le hz
  · norm_num
  by_cases hz1 : z≤1
  · have h := (Real.abs_log_mul_self_rpow_lt z (1/64) hz hz1 (by norm_num)).le
    norm_num at h
    have hp : 0≤z^(63/64:ℝ) := Real.rpow_nonneg hz.le _
    have he : z^(1/64:ℝ)*z^(63/64:ℝ)=z := by
      rw [←Real.rpow_add hz]
      norm_num
    have hh := mul_le_mul_of_nonneg_right h hp
    rw [abs_of_nonneg (Real.rpow_nonneg hz.le _),mul_assoc,he] at hh
    rw [abs_mul,abs_of_pos hz]
    rw [mul_comm (|Real.log z|) z] at hh
    nlinarith [sq_nonneg z]
  · have hz1 : 1≤z := le_of_lt (lt_of_not_ge hz1)
    have hlog : 0≤Real.log z := Real.log_nonneg hz1
    rw [abs_of_nonneg (mul_nonneg hz.le hlog)]
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hz) hz.le
    have hp : 0≤z^(63/64:ℝ) := Real.rpow_nonneg hz.le _
    nlinarith

theorem abs_mul_log_le_gaussian {u C x : ℝ} (hu : 0≤u) (hC : 0≤C)
    (hbound : u≤C*Real.exp (-(4/9:ℝ)*x^2)) :
    |u*Real.log u|≤(64*C^(63/64:ℝ)+C^2)*Real.exp (-(7/16:ℝ)*x^2) := by
  have hp := Real.rpow_le_rpow hu hbound (by norm_num : (0:ℝ)≤63/64)
  rw [Real.mul_rpow hC (Real.exp_pos _).le,←Real.exp_mul] at hp
  have he : (-(4/9:ℝ)*x^2)*(63/64)=-(7/16:ℝ)*x^2 := by ring
  rw [he] at hp
  have hs := pow_le_pow_left₀ hu hbound 2
  rw [mul_pow,←Real.exp_natCast_mul] at hs
  have hexp : Real.exp (2*(-(4/9:ℝ)*x^2))≤Real.exp (-(7/16:ℝ)*x^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg x]
  have hs' := hs.trans (mul_le_mul_of_nonneg_left hexp (sq_nonneg C))
  have h := abs_mul_log_le_rpow_add_sq hu
  nlinarith

def gibbsGaussianConstant (C : ℝ) : ℝ :=
  (64*C^(63/64:ℝ)+C^2)+C*|Real.log (Real.sqrt (2*Real.pi))|+2*C+
    (Real.sqrt (2*Real.pi))⁻¹+1

theorem gibbsGaussianConstant_pos {C : ℝ} (hC : 0<C) : 0<gibbsGaussianConstant C := by
  unfold gibbsGaussianConstant
  positivity

/-- Every density with the eventual `4/9` Gaussian envelope has an entropy
integrand envelope with exponent `7/16 > 3/7`. -/
theorem gibbsDefect_gaussian_envelope_bound {f : ℝ→ℝ} {C : ℝ} (hC : 0<C)
    (hf : ∀x,0≤f x) (henv : ∀x,f x≤C*Real.exp (-(4/9:ℝ)*x^2)) :
    ∀x, |gibbsDefect (f x) (gaussianPDFReal 0 1 x)|≤
      gibbsGaussianConstant C*(1+x^2)*Real.exp (-(7/16:ℝ)*x^2) := by
  let a : ℝ := |Real.log (Real.sqrt (2*Real.pi))|
  let b : ℝ := (Real.sqrt (2*Real.pi))⁻¹
  let E : ℝ := 64*C^(63/64:ℝ)+C^2
  let K : ℝ := E+C*a+2*C+b+1
  have ha : 0≤a := abs_nonneg _
  have hb : 0<b := by dsimp [b]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  intro x
  change |gibbsDefect (f x) (gaussianPDFReal 0 1 x)|≤K*(1+x^2)*Real.exp (-(7/16:ℝ)*x^2)
  let e := Real.exp (-(7/16:ℝ)*x^2)
  have he : 0<e := Real.exp_pos _
  have he1 : Real.exp (-(4/9:ℝ)*x^2)≤e := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg x]
  have he2 : Pang.gaussianWeight x≤e := by
    unfold Pang.gaussianWeight e
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg x]
  have hfx : f x≤C*e := (henv x).trans (mul_le_mul_of_nonneg_left he1 hC.le)
  have hφ : gaussianPDFReal 0 1 x≤b*e := by
    rw [standardGaussianPDF_eq]
    exact mul_le_mul_of_nonneg_left he2 hb.le
  have hlog : |Real.log (gaussianPDFReal 0 1 x)|≤a+x^2/2 := by
    rw [log_standardGaussianPDF]
    have ht := abs_sub (-Real.log (Real.sqrt (2*Real.pi))) (x^2/2)
    have hxdiv : |x^2/(2:ℝ)|=x^2/2 := abs_of_nonneg (by positivity)
    rw [abs_neg,hxdiv] at ht
    exact ht
  have hfLog := abs_mul_log_le_gaussian (hf x) hC.le (henv x)
  change |f x*Real.log (f x)-f x*Real.log (gaussianPDFReal 0 1 x)-f x+
      gaussianPDFReal 0 1 x|≤_
  calc
    _≤|f x*Real.log (f x)|+|f x*Real.log (gaussianPDFReal 0 1 x)|+|f x|+
        |gaussianPDFReal 0 1 x| := by
      calc
        _≤|f x*Real.log (f x)-f x*Real.log (gaussianPDFReal 0 1 x)-f x|+
            |gaussianPDFReal 0 1 x| := abs_add_le _ _
        _≤(|f x*Real.log (f x)-f x*Real.log (gaussianPDFReal 0 1 x)|+|f x|)+
            |gaussianPDFReal 0 1 x| := by gcongr; exact abs_sub _ _
        _≤_ := by gcongr; exact abs_sub _ _
    _≤E*e+(C*e)*(a+x^2/2)+C*e+b*e := by
      have hcross : |f x*Real.log (gaussianPDFReal 0 1 x)|≤(C*e)*(a+x^2/2) := by
        rw [abs_mul,abs_of_nonneg (hf x)]
        exact mul_le_mul hfx hlog (abs_nonneg _) (mul_nonneg hC.le he.le)
      simpa only [abs_of_nonneg (hf x),abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)] using
        add_le_add (add_le_add (add_le_add hfLog hcross) hfx) hφ
    _≤K*(1+x^2)*e := by
      have hh : E+C*(a+x^2/2)+C+b≤K*(1+x^2) := by
        dsimp [K]
        nlinarith [mul_nonneg hE (sq_nonneg x),mul_nonneg (mul_nonneg hC.le ha) (sq_nonneg x),
          mul_nonneg hb.le (sq_nonneg x),mul_nonneg hC.le (sq_nonneg x),sq_nonneg x]
      convert mul_le_mul_of_nonneg_right hh he.le using 1 <;> ring

theorem gibbsDefect_gaussian_envelope {f : ℝ→ℝ} {C : ℝ} (hC : 0<C)
    (hf : ∀x,0≤f x) (henv : ∀x,f x≤C*Real.exp (-(4/9:ℝ)*x^2)) :
    ∃K : ℝ, 0<K ∧ ∀x, |gibbsDefect (f x) (gaussianPDFReal 0 1 x)|≤
      K*(1+x^2)*Real.exp (-(7/16:ℝ)*x^2) :=
  ⟨gibbsGaussianConstant C,gibbsGaussianConstant_pos hC,
    gibbsDefect_gaussian_envelope_bound hC hf henv⟩

end
end ENT.Quantitative
