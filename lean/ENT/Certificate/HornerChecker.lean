module

public import ENT.Certificate.DensePolynomial
public import Mathlib.Tactic.NormNum

/-! Homogeneous Horner evaluation for Bernstein certificates. For a nonempty coefficient list B₀,…,B_D, the second component is the polynomial ∑ⱼ Bⱼ Xʲ (1−X)ᴰ⁻ʲ. Nonnegativity follows by the same recursion. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Certificate

def bernsteinHorner : List ℤ → IntPoly × IntPoly
  | [] => ([1], [])
  | [b] => ([1], [b])
  | b :: c :: bs =>
      let prev := bernsteinHorner (c :: bs)
      let nextPower := Dense.mul [1, -1] prev.1
      (nextPower, Dense.add (Dense.scale b nextPower) (0 :: prev.2))

def checkBernsteinHorner (d : ℕ) (p : IntPoly) (bs : List ℤ) : Bool :=
  decide (bs.length = d + 1) &&
    ((p == (bernsteinHorner bs).2) && bs.all (fun b => decide (0 ≤ b)))

theorem bernsteinHorner_nonneg (bs : List ℤ) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∀ b ∈ bs, 0 ≤ b) →
      0 ≤ eval (bernsteinHorner bs).1 x ∧ 0 ≤ eval (bernsteinHorner bs).2 x := by
  induction bs with
  | nil =>
      intro _
      simp [bernsteinHorner]
  | cons b bs ih =>
      intro hb
      have hb0 : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb b (by simp)
      cases bs with
      | nil => simpa [bernsteinHorner] using hb0
      | cons c bs =>
          have htail : ∀ a ∈ c :: bs, 0 ≤ a := fun a ha => hb a (by simp [ha])
          have hprev := ih htail
          have hnext :
              0 ≤ eval (Dense.mul [1, -1] (bernsteinHorner (c :: bs)).1) x := by
            rw [Dense.eval_mul]
            have hy : eval [1, -1] x = 1 - x := by simp; ring
            rw [hy]
            exact mul_nonneg (sub_nonneg.mpr hx1) hprev.1
          change 0 ≤ eval (Dense.mul [1, -1] (bernsteinHorner (c :: bs)).1) x ∧
            0 ≤ eval (Dense.add
              (Dense.scale b (Dense.mul [1, -1] (bernsteinHorner (c :: bs)).1))
              (0 :: (bernsteinHorner (c :: bs)).2)) x
          refine ⟨hnext, ?_⟩
          rw [Dense.eval_add, Dense.eval_scale, Dense.eval_cons]
          simp only [Int.cast_zero, zero_add]
          exact add_nonneg (mul_nonneg hb0 hnext) (mul_nonneg hx0 hprev.2)

theorem checkBernsteinHorner_sound (d : ℕ) (p : IntPoly) (bs : List ℤ)
    (h : checkBernsteinHorner d p bs = true)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ eval p x := by
  unfold checkBernsteinHorner at h
  have hparts := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2
  have hp : p = (bernsteinHorner bs).2 := by
    simpa only [beq_iff_eq] using hparts.1
  have hb : ∀ b ∈ bs, 0 ≤ b := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hparts.2
  rw [hp]
  exact (bernsteinHorner_nonneg bs x hx0 hx1 hb).2

end ENT.Certificate
