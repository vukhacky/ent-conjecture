module

public import ENT.Certificate.Bernstein
public import ENT.Certificate.HornerChecker

/-! Combines nonnegativity in the Bernstein representation with the spline and curvature identities on a cell. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Certificate

noncomputable section

def TransformIdentity (c : CellData) : Prop :=
  ∀ x : ℝ, eval c.transformedCoeffs x =
    if c.halfCell then (2 : ℝ) ^ c.degreeBound * eval c.rCoeffs (x / 2)
    else eval c.rCoeffs x

theorem cellConclusion_of_bernstein (c : CellData)
    (hn0 : 7 ≤ c.n) (hn1 : c.n ≤ 149) (hk : 2 * c.k < c.n)
    (hhalf : c.halfCell = true ↔ 2 * c.k + 1 = c.n)
    (hp : ∀ x : ℝ, eval c.pCoeffs x = splinePiece c.n c.k x)
    (hr : ∀ x : ℝ, eval c.rCoeffs x = targetPolynomial c.n c.k x)
    (ht : TransformIdentity c)
    (hc : checkBernsteinHorner c.degreeBound c.transformedCoeffs
      c.bernsteinNumerators = true) : CellConclusion c := by
  refine ⟨hn0, hn1, hk, hhalf, hp, hr, ?_⟩
  intro s hs0 hs1
  rw [← hr s]
  cases hflag : c.halfCell with
  | false =>
      have hs1' : s ≤ 1 := by simpa [width, hflag] using hs1
      have h := checkBernsteinHorner_sound c.degreeBound c.transformedCoeffs
        c.bernsteinNumerators hc s hs0 hs1'
      have hid : eval c.transformedCoeffs s = eval c.rCoeffs s := by
        simpa [TransformIdentity, hflag] using ht s
      rw [hid] at h
      exact h
  | true =>
      have hs1' : s ≤ 1 / 2 := by simpa [width, hflag] using hs1
      apply halfCell_nonneg (eval c.rCoeffs) (eval c.transformedCoeffs)
        ((2 : ℝ) ^ c.degreeBound) (pow_pos (by norm_num) _) ?_ ?_ s hs0 hs1'
      · intro x
        simpa [TransformIdentity, hflag] using ht x
      · intro x hx0 hx1
        exact checkBernsteinHorner_sound c.degreeBound c.transformedCoeffs
          c.bernsteinNumerators hc x hx0 hx1

end
end ENT.Certificate
