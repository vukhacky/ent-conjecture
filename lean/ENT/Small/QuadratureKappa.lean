module

public import ENT.Small.EnclosuresLogCertificate
public import ENT.Spline.SupportInterior

/-! Actual integral semantics for the local curvature coefficient kappa. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace ENT.Small
noncomputable section
open Spline Certificate Quadrature

def kappaIntegrand (n : ℕ) (t : ℝ) : ℝ :=
  (unitSumSplineDensity (n-2) (t-1)-unitSumSplineDensity n t)*Real.log (unitSumSplineDensity n t)

theorem intervalIntegrable_kappaIntegrand (n : ℕ) (hn : 4 ≤ n) :
    IntervalIntegrable (kappaIntegrand n) volume 0 (n:ℝ) := by
  apply (intervalIntegrable_log_unitSumSplineDensity n (by omega)).continuousOn_mul
  exact (((continuous_unitSumSplineDensity (n-2)).comp (continuous_id.sub continuous_const)).sub
    (continuous_unitSumSplineDensity n)).continuousOn

theorem kappaIntegrand_reflection (n : ℕ) (hn : 4 ≤ n) (t : ℝ) :
    kappaIntegrand n ((n:ℝ)-t) = kappaIntegrand n t := by
  unfold kappaIntegrand
  rw [unitSumSplineDensity_reflection n (by omega)]
  have he : (n:ℝ)-t-1 = ((n-2:ℕ):ℝ)-(t-1) := by
    rw [Nat.cast_sub (by omega : 2≤n),Nat.cast_ofNat]
    ring
  rw [he,unitSumSplineDensity_reflection (n-2) (by omega)]

theorem unitSumSplineDensity_eq_zero_of_nonpos (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : t ≤ 0) :
    unitSumSplineDensity n t = 0 := by
  rcases ht.eq_or_lt with h|h
  · rw [h,unitSumSplineDensity_zero n hn]
  · apply unitSumSplineDensity_eq_zero_of_not_mem n hn t
    intro hm
    linarith [hm.1]

theorem kappa_outer_integral (n : ℕ) (hn : 4 ≤ n) :
    (∫ t in (0:ℝ)..1,kappaIntegrand n t) =
      ((n-1:ℕ):ℝ)/((Nat.factorial (n-1):ℝ)*(n:ℝ)^2) +
        Real.log (Nat.factorial (n-1):ℝ)/((Nat.factorial (n-1):ℝ)*(n:ℝ)) := by
  have he : (∫ t in (0:ℝ)..1,kappaIntegrand n t) =
      -(∫ t in (0:ℝ)..1,unitSumSplineDensity n t*Real.log (unitSumSplineDensity n t)) := by
    rw [←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at ht
    dsimp only [kappaIntegrand]
    rw [unitSumSplineDensity_eq_zero_of_nonpos (n-2) (by omega) (t-1) (by linarith [ht.2])]
    ring
  rw [he,unitSum_entropy_outer_integral n (by omega)]
  ring

theorem smallKappa_formula_half (n : ℕ) (hn : 4 ≤ n) :
    smallKappa n = 1-2*(n:ℝ)*
      (((n-1:ℕ):ℝ)/((Nat.factorial (n-1):ℝ)*(n:ℝ)^2) +
        Real.log (Nat.factorial (n-1):ℝ)/((Nat.factorial (n-1):ℝ)*(n:ℝ)) +
        (∫ t in (1:ℝ)..((n:ℝ)/2),kappaIntegrand n t)) := by
  have hi := intervalIntegrable_kappaIntegrand n hn
  have he := integral_reflection_half (by positivity : (0:ℝ)≤n) hi (kappaIntegrand_reflection n hn)
  have hhalf : (1:ℝ)≤(n:ℝ)/2 := by
    have h : (2:ℝ)≤n := by exact_mod_cast (show 2≤n by omega)
    linarith
  have hi01 : IntervalIntegrable (kappaIntegrand n) volume 0 1 := hi.mono_set (by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1),uIcc_of_le (Nat.cast_nonneg n)]
    exact Icc_subset_Icc le_rfl (by exact_mod_cast (show 1 ≤ n by omega)))
  have hi1h : IntervalIntegrable (kappaIntegrand n) volume 1 ((n:ℝ)/2) := hi.mono_set (by
    rw [uIcc_of_le hhalf,uIcc_of_le (Nat.cast_nonneg n)]
    exact Icc_subset_Icc (by norm_num)
      (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]))
  have hs := intervalIntegral.integral_add_adjacent_intervals hi01 hi1h
  change 1-(n:ℝ)*(∫t in (0:ℝ)..(n:ℝ),kappaIntegrand n t) = _
  rw [he,←hs,kappa_outer_integral n hn]
  ring

theorem kappa_weight_cell_eq (n k : ℕ) (hn : 4 ≤ n) (hk0 : 1 ≤ k) (hk : k ≤ n-1)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    unitSumSplineDensity (n-2) ((k:ℝ)+x-1)-unitSumSplineDensity n ((k:ℝ)+x) =
      rationalPolynomial
        (Dense.add (Dense.scale (((n-1)*(n-2):ℕ):ℤ) (splineCoeffs (n-2) (k-1)))
          (Dense.scale (-1) (splineCoeffs n k))) (Nat.factorial (n-1):ℤ) x := by
  have he : (k:ℝ)+x-1 = ((k-1:ℕ):ℝ)+x := by
    rw [Nat.cast_sub hk0,Nat.cast_one]
    ring
  rw [he,unitSumSplineDensity_eq_rationalPolynomial (n-2) (k-1) (by omega) (by omega) x hx.1 hx.2,
    unitSumSplineDensity_eq_rationalPolynomial n k (by omega) (by omega) x hx.1 hx.2]
  have hf : (Nat.factorial (n-1):ℝ) = ((n-1:ℕ):ℝ)*((n-2:ℕ):ℝ)*(Nat.factorial (n-3):ℝ) := by
    have h1 : n-1=(n-2)+1 := by omega
    have h2 : n-2=(n-3)+1 := by omega
    have hf1 : (n-1).factorial=(n-1)*(n-2).factorial := by
      conv_lhs => rw [h1,Nat.factorial_succ]
      rw [←h1]
    have hf2 : (n-2).factorial=(n-2)*(n-3).factorial := by
      conv_lhs => rw [h2,Nat.factorial_succ]
      rw [←h2]
    rw [hf1,hf2]
    push_cast
    ring
  have hne : (Nat.factorial (n-3):ℝ)≠0 := by positivity
  have h1 : ((n-1:ℕ):ℝ)≠0 := by exact_mod_cast (show n-1≠0 by omega)
  have h2 : ((n-2:ℕ):ℝ)≠0 := by exact_mod_cast (show n-2≠0 by omega)
  simp only [rationalPolynomial,Dense.eval_add,Dense.eval_scale,Int.cast_natCast,Int.cast_mul,Int.cast_neg,
    Int.cast_one,Nat.cast_mul,neg_one_mul]
  rw [hf]
  have he3 : n-2-1=n-3 := by omega
  rw [he3]
  field_simp [hne,h1,h2]
  <;> ring

theorem kappa_logQuadrature_bound (c : LogQuadratureCell) (hc : c.Valid)
    (n k : ℕ) (hn : 4 ≤ n) (hk0 : 1 ≤ k) (hk : k ≤ n-1)
    (hp : c.densityCoeffs = splineCoeffs n k)
    (hD : c.densityDenominator = (Nat.factorial (n-1):ℤ))
    (hw : c.weightCoeffs = Dense.add
      (Dense.scale (((n-1)*(n-2):ℕ):ℤ) (splineCoeffs (n-2) (k-1)))
      (Dense.scale (-1) (splineCoeffs n k)))
    (hwd : c.weightDenominator = c.densityDenominator) (hb : c.b ≤ 1) :
    (c.lower:ℝ) ≤ (∫t in ((k:ℝ)+(c.a:ℝ))..((k:ℝ)+(c.b:ℝ)),kappaIntegrand n t) ∧
      (∫t in ((k:ℝ)+(c.a:ℝ))..((k:ℝ)+(c.b:ℝ)),kappaIntegrand n t) ≤ (c.upper:ℝ) := by
  have haR : (0:ℝ)≤c.a := by exact_mod_cast hc.1
  have hbR : (c.b:ℝ)≤1 := by exact_mod_cast hb
  have h := c.transfer hc (fun t : ℝ => unitSumSplineDensity n ((k:ℝ)+t))
    (fun t : ℝ => unitSumSplineDensity (n-2) ((k:ℝ)+t-1)-unitSumSplineDensity n ((k:ℝ)+t))
    (by
      intro x hx
      rw [hp,hD]
      exact unitSumSplineDensity_eq_rationalPolynomial n k (by omega) (by omega)
        x (haR.trans hx.1) (hx.2.trans hbR))
    (by
      intro x hx
      rw [hw,hwd,hD]
      exact kappa_weight_cell_eq n k hn hk0 hk x ⟨haR.trans hx.1,hx.2.trans hbR⟩)
  have he := intervalIntegral.integral_comp_add_left (f:=kappaIntegrand n)
    (a:=(c.a:ℝ)) (b:=(c.b:ℝ)) (k:ℝ)
  change (c.lower:ℝ) ≤ (∫t in (c.a:ℝ)..(c.b:ℝ),kappaIntegrand n ((k:ℝ)+t)) ∧
    (∫t in (c.a:ℝ)..(c.b:ℝ),kappaIntegrand n ((k:ℝ)+t)) ≤ (c.upper:ℝ) at h
  rwa [he] at h

end
end ENT.Small
