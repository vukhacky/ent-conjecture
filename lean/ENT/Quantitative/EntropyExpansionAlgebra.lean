module

public import ENT.Quantitative.EntropyExpansionTaylor

/-! Algebraic estimates separating the density approximation error from the
cubic entropy profile. All constants are explicit. -/

@[expose] public section
set_option autoImplicit false
namespace ENT.Quantitative
noncomputable section

theorem fourth_power_add_le (a b : ℝ) : (a+b)^4≤8*(a^4+b^4) := by
  nlinarith [sq_nonneg (a^2-b^2),sq_nonneg (a-b),sq_nonneg (a+b),
    sq_nonneg ((a-b)*(a+b)),sq_nonneg ((a-b)^2)]

/-- Density error `e` and profile `d` are kept separate to preserve the powers
of the Gaussian reference density in the subsequent integral estimates. -/
theorem gibbsDefect_profile_error {u v d e : ℝ} (hu : 0≤u) (hv : 0<v)
    (he : u=v*(1+d)+e) :
    |gibbsDefect u v-v*(d^2/2-d^3/6)|≤
      (8/3:ℝ)*v*d^4+(8/3:ℝ)*e^4/v^3+
      |d| *|e|+e^2/(2*v)+d^2*|e|/2+|d| *e^2/(2*v)+|e|^3/(6*v^2) := by
  let A := (u-v)^2/(2*v)-(u-v)^3/(6*v^2)
  have hT := gibbsDefect_cubic_error hu hv
  have h4 := fourth_power_add_le (v*d) e
  have huv : u-v=v*d+e := by linarith [he]
  have h4' : (u-v)^4/(3*v^3)≤(8/3:ℝ)*v*d^4+(8/3:ℝ)*e^4/v^3 := by
    rw [huv]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<3*v^3)).mpr
    field_simp
    nlinarith [h4]
  have hA : A-v*(d^2/2-d^3/6)=
      d*e+e^2/(2*v)-d^2*e/2-d*e^2/(2*v)-e^3/(6*v^2) := by
    dsimp [A]
    rw [huv]
    field_simp
    ring
  have habs : |A-v*(d^2/2-d^3/6)|≤
      |d| *|e|+e^2/(2*v)+d^2*|e|/2+|d| *e^2/(2*v)+|e|^3/(6*v^2) := by
    rw [hA]
    calc
      _≤|d*e|+|e^2/(2*v)|+|d^2*e/2|+|d*e^2/(2*v)|+|e^3/(6*v^2)| := by
        calc
          _≤|d*e+e^2/(2*v)-d^2*e/2-d*e^2/(2*v)|+|e^3/(6*v^2)| := abs_sub _ _
          _≤(|d*e+e^2/(2*v)-d^2*e/2|+|d*e^2/(2*v)|)+|e^3/(6*v^2)| := by gcongr; exact abs_sub _ _
          _≤((|d*e+e^2/(2*v)|+|d^2*e/2|)+|d*e^2/(2*v)|)+|e^3/(6*v^2)| := by gcongr; exact abs_sub _ _
          _≤_ := by gcongr; exact abs_add_le _ _
      _=_ := by simp only [abs_mul,abs_div,abs_pow,abs_of_pos hv,abs_of_pos (by norm_num : (0:ℝ)<2),
        abs_of_pos (by norm_num : (0:ℝ)<6),sq_abs]
  calc
    _≤|gibbsDefect u v-A|+|A-v*(d^2/2-d^3/6)| := abs_sub_le _ _ _
    _≤((8/3:ℝ)*v*d^4+(8/3:ℝ)*e^4/v^3)+
      (|d| *|e|+e^2/(2*v)+d^2*|e|/2+|d| *e^2/(2*v)+|e|^3/(6*v^2)) :=
      add_le_add (hT.trans h4') habs
    _=_ := by ring

/-- A directly usable bound after inserting an `M/n⁴` absolute density error
and a `P/n` polynomial profile bound. -/
theorem scaled_gibbsDefect_profile_error {u v d e P M n : ℝ}
    (hu : 0≤u) (hv : 0<v) (hn : 0<n) (hP : 0≤P) (hM : 0≤M)
    (he : u=v*(1+d)+e) (hd : |d|≤P/n) (herr : |e|≤M/n^4) :
    n^3*|gibbsDefect u v-v*(d^2/2-d^3/6)|≤
      (8/3:ℝ)*v*P^4/n+(8/3:ℝ)*M^4/(n^13*v^3)+
      P*M/n^2+M^2/(2*n^5*v)+P^2*M/(2*n^3)+P*M^2/(2*n^6*v)+M^3/(6*n^9*v^2) := by
  have h := gibbsDefect_profile_error hu hv he
  have hd2 : d^2≤(P/n)^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hd4 : d^4≤(P/n)^4 := by simpa only [pow_abs,abs_of_nonneg (show (0:ℝ)≤d^4 by positivity)] using pow_le_pow_left₀ (abs_nonneg d) hd 4
  have he2 : e^2≤(M/n^4)^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg e) herr 2
  have he3 : |e|^3≤(M/n^4)^3 := pow_le_pow_left₀ (abs_nonneg e) herr 3
  have he4 : e^4≤(M/n^4)^4 := by simpa only [pow_abs,abs_of_nonneg (show (0:ℝ)≤e^4 by positivity)] using pow_le_pow_left₀ (abs_nonneg e) herr 4
  have hh : |gibbsDefect u v-v*(d^2/2-d^3/6)|≤
      (8/3:ℝ)*v*(P/n)^4+(8/3:ℝ)*(M/n^4)^4/v^3+
      (P/n)*(M/n^4)+(M/n^4)^2/(2*v)+(P/n)^2*(M/n^4)/2+
      (P/n)*(M/n^4)^2/(2*v)+(M/n^4)^3/(6*v^2) := by
    apply h.trans
    gcongr
  have hh' := mul_le_mul_of_nonneg_left hh (pow_nonneg hn.le 3)
  convert hh' using 1
  field_simp <;> ring

end
end ENT.Quantitative
