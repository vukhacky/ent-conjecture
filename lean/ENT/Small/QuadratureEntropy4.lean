module

public import ENT.Small.EnclosuresLogCertificate
public import ENT.Small.LogQuadratureData.Entropy4Batch000

@[expose] public section
set_option autoImplicit false
open MeasureTheory
namespace ENT.Small
noncomputable section
open Spline Quadrature

theorem unitSum_entropy_middle_4_bounds :
    (-3274609141/10000000000:ℝ) ≤ (∫ x in (1:ℝ)..2, unitSumSplineDensity 4 x*Real.log (unitSumSplineDensity 4 x)) ∧
    (∫ x in (1:ℝ)..2, unitSumSplineDensity 4 x*Real.log (unitSumSplineDensity 4 x)) ≤ (-3274609139/10000000000:ℝ) := by
  have hf : Continuous (fun x : ℝ => unitSumSplineDensity 4 x * Real.log (unitSumSplineDensity 4 x)) := Real.continuous_mul_log.comp (continuous_unitSumSplineDensity 4)
  have h0 := entropy_logQuadrature_bound Certified.Entropy4Cell000 Certified.Entropy4Cell000_valid 4 1
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by rfl) (by rfl) (by decide +kernel)
  norm_num only [Certified.Entropy4Cell000,Nat.cast_ofNat,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at h0
  rcases h0 with ⟨hl0,hu0⟩
  have h1 := entropy_logQuadrature_bound Certified.Entropy4Cell001 Certified.Entropy4Cell001_valid 4 1
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by rfl) (by rfl) (by decide +kernel)
  norm_num only [Certified.Entropy4Cell001,Nat.cast_ofNat,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at h1
  rcases h1 with ⟨hl1,hu1⟩
  have h2 := entropy_logQuadrature_bound Certified.Entropy4Cell002 Certified.Entropy4Cell002_valid 4 1
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by rfl) (by rfl) (by decide +kernel)
  norm_num only [Certified.Entropy4Cell002,Nat.cast_ofNat,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at h2
  rcases h2 with ⟨hl2,hu2⟩
  have h3 := entropy_logQuadrature_bound Certified.Entropy4Cell003 Certified.Entropy4Cell003_valid 4 1
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by rfl) (by rfl) (by decide +kernel)
  norm_num only [Certified.Entropy4Cell003,Nat.cast_ofNat,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one] at h3
  rcases h3 with ⟨hl3,hu3⟩
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 1 (75/64:ℝ)) (hf.intervalIntegrable (75/64:ℝ) (89/64:ℝ))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 1 (89/64:ℝ)) (hf.intervalIntegrable (89/64:ℝ) (107/64:ℝ))
  have hs3 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 1 (107/64:ℝ)) (hf.intervalIntegrable (107/64:ℝ) 2)
  constructor <;> linarith

end
end ENT.Small
