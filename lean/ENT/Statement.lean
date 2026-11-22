module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! Uniform product laws, finite differential entropy, and the ENT statement. -/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators ENNReal

namespace ENT

noncomputable section

def uniformUnit : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)

def cubeLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => uniformUnit)

def projection {n : ℕ} (a x : Fin n → ℝ) : ℝ :=
  ∑ i, a i * x i

def projectionLaw {n : ℕ} (a : Fin n → ℝ) : Measure ℝ :=
  (cubeLaw n).map (projection a)

def IsUnit {n : ℕ} (a : Fin n → ℝ) : Prop :=
  ∑ i, (a i) ^ 2 = 1

def diagonal (n : ℕ) : Fin n → ℝ :=
  fun _ => (Real.sqrt (n : ℝ))⁻¹

def IsDiagonal {n : ℕ} (a : Fin n → ℝ) : Prop :=
  ∀ i, (a i) ^ 2 = (n : ℝ)⁻¹

def deficit {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, ((a i) ^ 2 - (n : ℝ)⁻¹) ^ 2

/-- An actual probability density for a specified law, with finite entropy.
The explicit fields prevent a totalized, nonintegrable integral from being used
as the entropy of a probability distribution. -/
structure FiniteEntropyDensity (μ : Measure ℝ) where
  density : ℝ → ℝ
  nonneg : ∀ x, 0 ≤ density x
  measurable : Measurable density
  integrable : Integrable density volume
  mass_one : (∫ x, density x) = 1
  law_eq : μ = volume.withDensity (fun x => ENNReal.ofReal (density x))
  entropy_integrable :
    Integrable (fun x => density x * Real.log (density x)) volume

def FiniteEntropyDensity.entropy {μ : Measure ℝ}
    (p : FiniteEntropyDensity μ) : ℝ :=
  -(∫ x, p.density x * Real.log (p.density x))

def DensityExistence : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a : Fin n → ℝ, IsUnit a →
    Nonempty (FiniteEntropyDensity (projectionLaw a))

def EntropyLawInvariance : Prop :=
  ∀ (μ : Measure ℝ) (p q : FiniteEntropyDensity μ),
    p.entropy = q.entropy

/-- ENT in one ambient dimension, including existence, finiteness and equality.
The existential density bundles are deliberate: universal quantification over
unproved-to-exist density bundles could otherwise give a vacuous statement. -/
def ENTAt (n : ℕ) : Prop :=
  ∀ a : Fin n → ℝ, IsUnit a →
    ∃ p : FiniteEntropyDensity (projectionLaw a),
    ∃ q : FiniteEntropyDensity (projectionLaw (diagonal n)),
      p.entropy ≤ q.entropy ∧
        (p.entropy = q.entropy ↔ IsDiagonal a)

def FiniteStatement : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ 149 → ENTAt n

/-- An explicit open mathematical dependency, not an axiom declaration. -/
def PangTail : Prop :=
  ∀ n : ℕ, 150 ≤ n → ENTAt n

def MainStatement : Prop :=
  ∀ n : ℕ, 0 < n → ENTAt n

end
end ENT
