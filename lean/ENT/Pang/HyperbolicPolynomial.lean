module

public import ENT.Pang.Tilt
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic.FinCases

/-! Finite derivative certificates for hyperbolic-polynomial inequalities. -/

@[expose] public section

set_option autoImplicit false

open Set Polynomial

namespace ENT.Pang

noncomputable section

def hyperbolicPoly (a : ℝ) (p q : Polynomial ℝ) (t : ℝ) : ℝ :=
  p.eval t * Real.cosh (a * t) + q.eval t * Real.sinh (a * t)

theorem hasDerivAt_hyperbolicPoly (a : ℝ) (p q : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (hyperbolicPoly a p q)
      (hyperbolicPoly a (p.derivative + C a * q) (q.derivative + C a * p) t) t := by
  have hc := (Real.hasDerivAt_cosh (a * t)).comp t ((hasDerivAt_id t).const_mul a)
  have hs := (Real.hasDerivAt_sinh (a * t)).comp t ((hasDerivAt_id t).const_mul a)
  have h := ((p.hasDerivAt t).mul hc).add ((q.hasDerivAt t).mul hs)
  apply h.congr_deriv
  simp only [hyperbolicPoly, eval_add, eval_mul, eval_C, Function.comp_apply]
  ring

theorem positive_of_positive_derivative {f g : ℝ → ℝ}
    (hf : ∀ x : ℝ, HasDerivAt f (g x) x) (hzero : f 0 = 0)
    (hpos : ∀ x : ℝ, 0 < x → 0 < g x) {t : ℝ} (ht : 0 < t) : 0 < f t := by
  have hm : StrictMonoOn f (Ici (0 : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · intro x _
      exact (hf x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici, mem_Ioi] at hx
      rw [(hf x).deriv]
      exact hpos x hx
  simpa only [hzero] using hm (show (0 : ℝ) ∈ Ici 0 by simp) ht.le ht

end
end ENT.Pang
