module

public import ENT.Small.EnclosuresThree
public import ENT.Spline.DensityLaw

/-! Canonical actual constants for the four-dimensional local argument.
Their scalar enclosures are supplied by the weighted-log quadrature modules. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory

namespace ENT.Small
noncomputable section

def fourV : ℝ := Real.log 6
def fourH : ℝ := (Spline.diagonalFiniteEntropyDensity 4 (by decide)).entropy
def fourJ2 : ℝ := ∫ x in (0:ℝ)..1, (1-x)*Spline.diagonalSplinePotential 4 x
def fourJ3 : ℝ := ∫ x in (0:ℝ)..1, Spline.diagonalSplinePotential 4 x
def fourF2R : ℝ := fourJ2 + fourJ3 + fourV/2 + 3/4

def fourAlpha : ℝ := 1/4 - fourH + 2*fourJ2
def fourC : ℝ := 12*fourH + 8*fourJ2 - 8*fourF2R
def fourE : ℝ := fourH - fourJ3
def fourK : ℝ := 16*fourH + (16/3)*fourJ3

theorem four_potential_one_tenth_bound :
    -Real.log ((3943:ℝ)/6000) ≤ (421/1000:ℝ) := by
  have h := Enclosures.log_ratio_taylor_bounds (x := (2057:ℝ)/9943)
    (by norm_num) (by norm_num) 5
  norm_num [Enclosures.artanhTaylor, Enclosures.artanhError, Finset.sum_range_succ] at h
  have he : -Real.log ((3943:ℝ)/6000) = Real.log ((6000:ℝ)/3943) := by
    rw [← Real.log_inv]
    norm_num
  rw [he]
  linarith [h.2]

end
end ENT.Small
