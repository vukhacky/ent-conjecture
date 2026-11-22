module

public import ENT.Quantitative.LargeAsymptotic
public import ENT.Quantitative.StabilityFinite

/-! Closed large-dimensional KL-enhanced stability and the asymptotic coefficient 3/50. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace ENT.Quantitative
noncomputable section

theorem KLStabilityAt.mono {n : ℕ} {β γ : ℝ} (h : KLStabilityAt n β) (hγβ : γ≤β) :
    KLStabilityAt n γ := by
  intro a ha
  obtain ⟨p,q,hKL,hgap⟩ := h a ha
  refine ⟨p,q,hKL,?_⟩
  have hδ := mul_le_mul_of_nonneg_right hγβ (deficit_nonneg a)
  linarith

theorem kl_stability_ge_256 {n : ℕ} (hn : 256≤n) :
    KLStabilityAt n (7/(180*(n:ℝ))) :=
  klStabilityAt_of_curvature (by omega) 7 (large_curvature_ge_256 hn)

theorem entropy_stability_ge_256 {n : ℕ} (hn : 256≤n) :
    EntropyStabilityAt n (7/(180*(n:ℝ))) :=
  (kl_stability_ge_256 hn).entropyStabilityAt

/-- Every coefficient strictly below 3/50 is uniformly valid in all sufficiently
large dimensions, and the entropy gap retains the nonnegative KL term. -/
theorem asymptotic_kl_stability {η : ℝ} (hη : 0<η) :
    ∃ N : ℕ, 256≤N ∧ ∀ n : ℕ, N≤n → KLStabilityAt n ((3/50-η)/(n:ℝ)) := by
  let ε : ℝ := min (1/10) (50*η/3)
  have hε : 0<ε := lt_min (by norm_num) (by positivity)
  have hεsmall : ε≤1/10 := min_le_left _ _
  have hεη : ε≤50*η/3 := min_le_right _ _
  obtain ⟨N,hN,hcurv⟩ := large_curvature_eventually hε hεsmall
  refine ⟨N,hN,?_⟩
  intro n hn
  have h := klStabilityAt_of_curvature (by omega : 5≤n) ((54/5)*(1-ε)) (hcurv n hn)
  apply h.mono
  have hnR : (0:ℝ)≤n := Nat.cast_nonneg n
  have hc : (3/50:ℝ)-η ≤ (3/50)*(1-ε) := by linarith
  convert div_le_div_of_nonneg_right hc hnR using 1 <;> ring

theorem asymptotic_entropy_stability {η : ℝ} (hη : 0<η) :
    ∃ N : ℕ, 256≤N ∧ ∀ n : ℕ, N≤n → EntropyStabilityAt n ((3/50-η)/(n:ℝ)) := by
  obtain ⟨N,hN,h⟩ := asymptotic_kl_stability hη
  exact ⟨N,hN,fun n hn=>(h n hn).entropyStabilityAt⟩

universe u

theorem iid_kl_stability_ge_256_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 256≤n)
    (U : Fin n→Ω→ℝ) (hU : ∀ i, AEMeasurable (U i) μ)
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i)=uniformUnit)
    (a : Fin n→ℝ) (ha : IsUnit a) :
    ∃ p : FiniteEntropyDensity (μ.map (fun ω=>∑ i,a i*U i ω)),
    ∃ q : FiniteEntropyDensity (μ.map (fun ω=>(Real.sqrt (n:ℝ))⁻¹*∑ i,U i ω)),
    ∃ hKL : FiniteKLData p q,
      (7/(180*(n:ℝ)))*deficit a+hKL.klDivergence≤q.entropy-p.entropy :=
  iid_kl_stability_of_ae μ U hU hind hlaw (kl_stability_ge_256 hn) a ha

end
end ENT.Quantitative
