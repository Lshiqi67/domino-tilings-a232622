module

public import Domino.ThreeRows.Main
public import Domino.ThreeRows.Boundary

/-! T03：由主生成函数取系数，得到七阶递推及完整七项初值。 -/

@[expose] public section

namespace Domino

open PowerSeries

noncomputable def orbitLag (n k : ℕ) : ℚ := if k ≤ n then (a (n - k) : ℚ) else 0

theorem orbit_coefficient_equation (n : ℕ) :
    (a n : ℚ) - 5 * orbitLag n 1 + orbitLag n 2 + 19 * orbitLag n 3 -
      19 * orbitLag n 4 - orbitLag n 5 + 5 * orbitLag n 6 - orbitLag n 7 =
      coeff n orbitNumerator := by
  have h := congrArg (coeff n) orbit_series_identity
  simpa only [orbitDenom_expanded, add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_ofNat_mul, coeff_X_mul_at, coeff_X_pow_mul', coeff_orbitSeries, orbitLag] using h

theorem orbit_recurrence_seven_rat (n : ℕ) :
    (a (n + 7) : ℚ) = 5 * (a (n + 6) : ℚ) - a (n + 5) - 19 * a (n + 4) +
      19 * a (n + 3) + a (n + 2) - 5 * a (n + 1) + a n := by
  have h := orbit_coefficient_equation (n + 7)
  simp (disch := omega) only [orbitLag, orbitNumerator, map_add, map_sub, coeff_ofNat_mul,
    coeff_one, coeff_X, coeff_X_pow, ite_eq_left, ite_eq_right] at h
  rw [show n + 7 - 1 = n + 6 by omega, show n + 7 - 2 = n + 5 by omega,
    show n + 7 - 3 = n + 4 by omega, show n + 7 - 4 = n + 3 by omega,
    show n + 7 - 5 = n + 2 by omega, show n + 7 - 6 = n + 1 by omega,
    show n + 7 - 7 = n by omega] at h
  linarith

theorem orbit_recurrence_seven (n : ℕ) :
    (a (n + 7) : ℤ) = 5 * (a (n + 6) : ℤ) - a (n + 5) - 19 * a (n + 4) +
      19 * a (n + 3) + a (n + 2) - 5 * a (n + 1) + a n := by
  exact_mod_cast orbit_recurrence_seven_rat n

theorem orbit_recurrence_seven_add (n : ℕ) :
    a (n + 7) + a (n + 5) + 19 * a (n + 4) + 5 * a (n + 1) =
      5 * a (n + 6) + 19 * a (n + 3) + a (n + 2) + a n := by
  have h := orbit_recurrence_seven n
  omega

theorem orbit_initial_values :
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 14 ∧ a 4 = 46 ∧ a 5 = 156 ∧ a 6 = 561 := by
  have h0 := orbit_coefficient_equation 0
  have h1 := orbit_coefficient_equation 1
  have h2 := orbit_coefficient_equation 2
  have h3 := orbit_coefficient_equation 3
  have h4 := orbit_coefficient_equation 4
  have h5 := orbit_coefficient_equation 5
  have h6 := orbit_coefficient_equation 6
  norm_num only [orbitLag, orbitNumerator, map_add, map_sub, coeff_ofNat_mul,
    coeff_one, coeff_X, coeff_X_pow, ite_true, ite_false] at h0 h1 h2 h3 h4 h5 h6
  have e0 : (a 0 : ℚ) = 1 := by linarith
  have e1 : (a 1 : ℚ) = 2 := by linarith
  have e2 : (a 2 : ℚ) = 5 := by linarith
  have e3 : (a 3 : ℚ) = 14 := by linarith
  have e4 : (a 4 : ℚ) = 46 := by linarith
  have e5 : (a 5 : ℚ) = 156 := by linarith
  have e6 : (a 6 : ℚ) = 561 := by linarith
  exact_mod_cast (show (a 0 : ℚ) = 1 ∧ (a 1 : ℚ) = 2 ∧ (a 2 : ℚ) = 5 ∧
    (a 3 : ℚ) = 14 ∧ (a 4 : ℚ) = 46 ∧ (a 5 : ℚ) = 156 ∧ (a 6 : ℚ) = 561 from
    ⟨e0, e1, e2, e3, e4, e5, e6⟩)

theorem orbit_recurrence_first : a 7 = 2037 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := orbit_initial_values
  have h := orbit_recurrence_seven_add 0
  simp only [zero_add, h0, h1, h2, h3, h4, h5, h6] at h
  norm_num at h
  omega

theorem three_row_main_theorem :
    orbitDenom * orbitSeries = orbitNumerator ∧
    orbitSeries = orbitNumerator * orbitDenom⁻¹ ∧
    (∀ n : ℕ, (a (n + 7) : ℤ) = 5 * (a (n + 6) : ℤ) - a (n + 5) - 19 * a (n + 4) +
      19 * a (n + 3) + a (n + 2) - 5 * a (n + 1) + a n) ∧
    (a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 14 ∧ a 4 = 46 ∧ a 5 = 156 ∧ a 6 = 561) :=
  ⟨orbit_series_identity, orbit_series_rational, orbit_recurrence_seven, orbit_initial_values⟩

end Domino
