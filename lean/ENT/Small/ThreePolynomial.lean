module

public import ENT.Small.OcticMoments
public import ENT.Comparison.CompactBalancing

/-! Exact homogeneous positivity identity for the dimension-three octic
approximant, including the ordering and simplex reduction. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ENT.Small
noncomputable section
open ENT.Comparison

def threeHomogeneousF (x y z : ℝ) : ℝ :=
  ((69 / 200 : ℝ) + 3 * (81 / 1000) + 15 * (-113 / 5000) + 105 * (221 / 100000)) *
    (x + y + z) ^ 4 -
  ((6 / 5 : ℝ) * (81 / 1000) + 18 * (-113 / 5000) + 252 * (221 / 100000)) *
    (x + y + z) ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) +
  ((48 / 7 : ℝ) * (-113 / 5000) + 192 * (221 / 100000)) *
    (x + y + z) * (x ^ 3 + y ^ 3 + z ^ 3) +
  ((252 / 5 : ℝ) * (221 / 100000)) * (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 -
  ((432 / 5 : ℝ) * (221 / 100000)) * (x ^ 4 + y ^ 4 + z ^ 4)

def threeHomogeneousGap (x y z : ℝ) : ℝ :=
  threeHomogeneousF (1 / 3) (1 / 3) (1 / 3) * (x + y + z) ^ 4 -
    threeHomogeneousF x y z -
    (1 / 100 : ℝ) * (x ^ 2 + y ^ 2 + z ^ 2 - (x + y + z) ^ 2 / 3) *
      (x + y + z) ^ 2

def threePositiveCertificate (x y z : ℝ) : ℝ :=
  4799 * x ^ 4 + 58297 * x ^ 3 * y + 131163 * x ^ 2 * y ^ 2 +
    145732 * x * y ^ 3 + 72866 * y ^ 4 +
    z * (97398 * x ^ 3 + 311562 * x ^ 2 * y + 350298 * x * y ^ 2 + 233532 * y ^ 3) +
    165465 * z ^ 2 * (x ^ 2 + x * y + y ^ 2)

theorem three_polynomial_identity (x y z : ℝ) :
    1312500 * threeHomogeneousGap (x + y + z) (y + z) z =
      threePositiveCertificate x y z := by
  unfold threeHomogeneousGap threeHomogeneousF threePositiveCertificate
  ring

theorem threePositiveCertificate_nonneg {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 0 ≤ threePositiveCertificate x y z := by
  unfold threePositiveCertificate
  positivity

theorem three_gap_nonneg_ordered {x y z : ℝ}
    (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) : 0 ≤ threeHomogeneousGap x y z := by
  have hi := three_polynomial_identity (x - y) (y - z) z
  have hp := threePositiveCertificate_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr hzy) hz
  rw [show x - y + (y - z) + z = x by ring, show y - z + z = y by ring] at hi
  linarith

theorem three_gap_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ threeHomogeneousGap x y z := by
  rcases le_total y x with hyx | hxy
  · rcases le_total z y with hzy | hyz
    · exact three_gap_nonneg_ordered hz hzy hyx
    · rcases le_total z x with hzx | hxz
      · convert three_gap_nonneg_ordered hy hyz hzx using 1 <;>
          unfold threeHomogeneousGap threeHomogeneousF <;> ring
      · convert three_gap_nonneg_ordered hy hyx hxz using 1 <;>
          unfold threeHomogeneousGap threeHomogeneousF <;> ring
  · rcases le_total z x with hzx | hxz
    · convert three_gap_nonneg_ordered hz hzx hxy using 1 <;>
        unfold threeHomogeneousGap threeHomogeneousF <;> ring
    · rcases le_total z y with hzy | hyz
      · convert three_gap_nonneg_ordered hx hxz hzy using 1 <;>
          unfold threeHomogeneousGap threeHomogeneousF <;> ring
      · convert three_gap_nonneg_ordered hx hxy hyz using 1 <;>
          unfold threeHomogeneousGap threeHomogeneousF <;> ring

theorem three_gap_eq_weight_gap (w : Fin 3 → ℝ) (hs : (∑ i, w i) = 1) :
    threeHomogeneousGap (w 0) (w 1) (w 2) =
      octicWeightExpression (69 / 200) (81 / 1000) (-113 / 5000) (221 / 100000) (flatWeights 3) -
      octicWeightExpression (69 / 200) (81 / 1000) (-113 / 5000) (221 / 100000) w -
        (1 / 100 : ℝ) * (powerSum w 2 - 1 / 3) := by
  have hs' : w 0 + w 1 + w 2 = 1 := by simpa only [Fin.sum_univ_three] using hs
  unfold threeHomogeneousGap threeHomogeneousF
  rw [hs']
  norm_num [octicWeightExpression, powerSum, flatWeights, Fin.sum_univ_three]

theorem three_octic_moment_comparison (a : Fin 3 → ℝ) (ha : IsUnit a) :
    (1 / 100 : ℝ) * deficit a ≤
      (∫ x, octicPolynomial (69 / 200) (81 / 1000) (-113 / 5000) (221 / 100000) x
        ∂varianceOneProjectionLaw (diagonal 3)) -
      (∫ x, octicPolynomial (69 / 200) (81 / 1000) (-113 / 5000) (221 / 100000) x
        ∂varianceOneProjectionLaw a) := by
  have h := three_gap_nonneg (sq_nonneg (a 0)) (sq_nonneg (a 1)) (sq_nonneg (a 2))
  rw [three_gap_eq_weight_gap (fun i => (a i) ^ 2) ha] at h
  have hdiag : (fun i : Fin 3 => (diagonal 3 i) ^ 2) = flatWeights 3 :=
    funext (diagonal_sq 3)
  rw [octicPolynomial_expectation _ (isUnit_diagonal (by decide)),
    octicPolynomial_expectation a ha, hdiag]
  have hdef : deficit a = powerSum (fun i => (a i) ^ 2) 2 - 1 / 3 := by
    rw [deficit_eq_sum_pow_four_sub_inv (by decide) ha]
    simp only [powerSum, ← pow_mul]
    norm_num
  rw [hdef]
  linarith

end
end ENT.Small
