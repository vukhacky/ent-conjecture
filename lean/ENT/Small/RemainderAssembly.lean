module

public import ENT.Small.StepEnvelope
public import ENT.Small.EnclosuresLogCertificate

/-! Assembly of a genuine remainder envelope from rational derivative grids,
exact cell geometry, primitive-based areas and a proved rational sum bound. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace ENT.Small
noncomputable section
open Quadrature

def remainderEndpoint (i : ℕ) : ℝ := 1 / 2 + (i : ℝ) / 64

theorem remainderEndpoint_monotone : Monotone remainderEndpoint := by
  intro i j hij
  have h : (i : ℝ) / 64 ≤ (j : ℝ) / 64 :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by norm_num)
  unfold remainderEndpoint
  linarith

private theorem expandedStep_sound_with_endpoints (n : ℕ) (g : DerivativeGrid)
    (hg : g.Valid) (hgn : g.n = n) (c : ExpandedStep) (hc : c.Valid g)
    (γ a b : ℝ) (hγ : (c.gamma : ℝ) = γ) (ha : (c.a : ℝ) = a)
    (hb : (c.b : ℝ) = b) (v : ℝ)
    (hv : v ∈ Icc ((1 - γ) * a) (min ((n : ℝ) / 2) ((1 + γ) * b))) :
    |logThirdUnitSum n v| ≤ (c.bound : ℝ) := by
  have h := c.sound g hg hc v
  rw [hgn] at h
  apply h
  simpa only [ExpandedStep.lowerLimit, ExpandedStep.upperLimit,
    Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_min, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_add, hγ, ha, hb] using hv

theorem remainderBound_from_grid (n : ℕ) (hn : 2 ≤ n) (N : ℕ)
    (g : DerivativeGrid) (hg : g.Valid) (hgn : g.n = n)
    (γ : ℚ) (hγ : (γ : ℝ) ∈ Ico (0 : ℝ) 1)
    (d : ℚ) (hd : 0 ≤ d)
    (hformula : ∀ v ∈ Ioc (0 : ℝ) 1, logThirdUnitSum n v = (d : ℝ) / v ^ 3)
    (S : Fin N → ExpandedStep) (A : Fin N → CubeAreaCertificate)
    (hS : ∀ i, (S i).Valid g) (hA : ∀ i, (A i).Valid)
    (hgeometry : ∀ i : Fin N,
      (S i).a = (1 / 2 : ℚ) + (i : ℚ) / 64 ∧
      (S i).b = (1 / 2 : ℚ) + ((i : ℚ) + 1) / 64 ∧
      (S i).gamma = γ ∧ (A i).n = n ∧
      ((A i).k : ℚ) + (A i).a = (S i).a ∧
      ((A i).k : ℚ) + (A i).b = (S i).b)
    (hend : (1 / 2 : ℚ) + (N : ℚ) / 64 = (n : ℚ) / 2)
    (U : ℚ)
    (hnumeric : 2 * (d / (1 - γ) ^ 3) *
        (1 / ((n : ℚ) * (Nat.factorial (n - 1) : ℚ) * 2 ^ n)) +
      2 * (∑ i : Fin N, (S i).bound * (A i).area) ≤ U) :
    ∃ H : LogThirdEnvelope n (γ : ℝ), averagedRemainderBound n H.bound ≤ (U : ℝ) := by
  let B : Fin N → ℝ := fun i => ((S i).bound : ℝ)
  let C : ℝ := (d : ℝ) / (1 - (γ : ℝ)) ^ 3
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hB : ∀ i, 0 ≤ B i := by
    intro i
    exact Rat.cast_nonneg.mpr (hS i).1
  have hC : 0 ≤ C :=
    div_nonneg hdR (pow_nonneg (sub_nonneg.mpr hγ.2.le) 3)
  have hstart : remainderEndpoint 0 = 1 / 2 := by norm_num [remainderEndpoint]
  have hendR : remainderEndpoint N = (n : ℝ) / 2 := by
    unfold remainderEndpoint
    have h := congrArg (fun q : ℚ => (q : ℝ)) hend
    push_cast at h
    exact h
  have hleft (i : Fin N) : ((S i).a : ℝ) = remainderEndpoint i := by
    unfold remainderEndpoint
    have h := congrArg (fun q : ℚ => (q : ℝ)) (hgeometry i).1
    push_cast at h
    exact h
  have hright (i : Fin N) : ((S i).b : ℝ) = remainderEndpoint (i + 1) := by
    simp only [remainderEndpoint, Nat.cast_add, Nat.cast_one]
    have h := congrArg (fun q : ℚ => (q : ℝ)) (hgeometry i).2.1
    push_cast at h
    exact h
  have hgam (i : Fin N) : ((S i).gamma : ℝ) = (γ : ℝ) := by
    exact_mod_cast (hgeometry i).2.2.1
  have houter : ∀ t ∈ Ioc (0 : ℝ) (1 / 2),
      ∀ v ∈ Icc ((1 - (γ : ℝ)) * t) (min ((n : ℝ) / 2) ((1 + (γ : ℝ)) * t)),
        |logThirdUnitSum n v| ≤ C / t ^ 3 :=
    outer_moving_bound hγ hdR hformula
  have hcell : ∀ i : Fin N,
      ∀ v ∈ Icc ((1 - (γ : ℝ)) * remainderEndpoint i)
        (min ((n : ℝ) / 2) ((1 + (γ : ℝ)) * remainderEndpoint (i + 1))),
        |logThirdUnitSum n v| ≤ B i := by
    intro i v hv
    exact expandedStep_sound_with_endpoints n g hg hgn (S i) (hS i)
      (γ : ℝ) (remainderEndpoint i) (remainderEndpoint (i + 1))
      (hgam i) (hleft i) (hright i) v hv
  have harea : ∀ i : Fin N,
      (∫ t in remainderEndpoint i..remainderEndpoint (i + 1),
        Spline.unitSumSplineDensity n t * t ^ 3) = ((A i).area : ℝ) := by
    intro i
    rcases hgeometry i with ⟨ha, hb, hγi, hni, hAa, hAb⟩
    have hla : ((A i).k : ℝ) + ((A i).a : ℝ) = remainderEndpoint i := by
      unfold remainderEndpoint
      have h := congrArg (fun q : ℚ => (q : ℝ)) (hAa.trans ha)
      push_cast at h
      exact h
    have hlb : ((A i).k : ℝ) + ((A i).b : ℝ) = remainderEndpoint (i + 1) := by
      simp only [remainderEndpoint, Nat.cast_add, Nat.cast_one]
      have h := congrArg (fun q : ℚ => (q : ℝ)) (hAb.trans hb)
      push_cast at h
      exact h
    have h := (A i).sound (hA i)
    rwa [hni, hla, hlb] at h
  let H : LogThirdEnvelope n (γ : ℝ) :=
    stepLogThirdEnvelope n hn (γ : ℝ) hγ remainderEndpoint B C hstart hendR
      hB hC houter hcell
  refine ⟨H, ?_⟩
  change averagedRemainderBound n (stepEnvelopeBound remainderEndpoint B C) ≤ (U : ℝ)
  rw [averagedRemainderBound_step_eq n hn remainderEndpoint remainderEndpoint_monotone
    B C hstart hendR, integral_unitSumSplineDensity_half n hn]
  simp_rw [harea]
  dsimp only [B, C]
  have h := (Rat.cast_le (K := ℝ)).mpr hnumeric
  push_cast at h
  exact h

end
end ENT.Small
