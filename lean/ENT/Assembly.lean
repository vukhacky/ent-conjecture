module

public import ENT.Statement

@[expose] public section

/-! Combination of the finite-dimensional and large-dimensional entropy comparisons. -/

set_option autoImplicit false

namespace ENT

theorem assembleFinite
    (one : ENTAt 1)
    (two : ENTAt 2)
    (small : ∀ n : ℕ, 3 ≤ n → n ≤ 6 → ENTAt n)
    (medium : ∀ n : ℕ, 7 ≤ n → n ≤ 149 → ENTAt n) :
    FiniteStatement := by
  intro n hn htop
  by_cases h1 : n = 1
  · subst n
    exact one
  by_cases h2 : n = 2
  · subst n
    exact two
  by_cases h6 : n ≤ 6
  · exact small n (by omega) h6
  · exact medium n (by omega) htop

/-- A conditional milestone only: no proof of `PangTail` is supplied here. -/
theorem assembleAllDimensions
    (finitePart : FiniteStatement) (pangTail : PangTail) : MainStatement := by
  intro n hn
  by_cases h : n ≤ 149
  · exact finitePart n hn h
  · exact pangTail n (by omega)

end ENT
