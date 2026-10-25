module

public import Domino.FiveRows.Main

/-! 从真实轨道的形式幂级数取系数：十四阶递推、完整初值及首个递推点。 -/

@[expose] public section

namespace Domino.FiveRows

open PowerSeries

set_option maxHeartbeats 2000000

noncomputable def orbitLag (n k : ℕ) : ℚ := if k ≤ n then (a5 (n - k) : ℚ) else 0

theorem orbit_coefficient_equation (n : ℕ) :
    (a5 n : ℚ) - 18 * orbitLag n 1 + 63 * orbitLag n 2 + 144 * orbitLag n 3 - 1060 * orbitLag n 4 + 1296 * orbitLag n 5 + 1312 * orbitLag n 6 - 3492 * orbitLag n 7 + 1312 * orbitLag n 8 + 1296 * orbitLag n 9 - 1060 * orbitLag n 10 + 144 * orbitLag n 11 + 63 * orbitLag n 12 - 18 * orbitLag n 13 + orbitLag n 14 = coeff n (numeratorA X) := by
  have h := congrArg (coeff n) orbit_series_identity
  simpa only [denominator_expanded, add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_ofNat_mul, coeff_X_mul_at, coeff_X_pow_mul', orbitSeries, coeff_countSeries, orbitLag] using h

theorem orbit_recurrence_fourteen_rat (n : ℕ) :
    (a5 (n + 14) : ℚ) = 18 * (a5 (n + 13) : ℚ) - 63 * (a5 (n + 12) : ℚ) - 144 * (a5 (n + 11) : ℚ) + 1060 * (a5 (n + 10) : ℚ) - 1296 * (a5 (n + 9) : ℚ) - 1312 * (a5 (n + 8) : ℚ) + 3492 * (a5 (n + 7) : ℚ) - 1312 * (a5 (n + 6) : ℚ) - 1296 * (a5 (n + 5) : ℚ) + 1060 * (a5 (n + 4) : ℚ) - 144 * (a5 (n + 3) : ℚ) - 63 * (a5 (n + 2) : ℚ) + 18 * (a5 (n + 1) : ℚ) - (a5 n : ℚ) := by
  have h := orbit_coefficient_equation (n + 14)
  simp (disch := omega) only [orbitLag, numeratorA, map_add, map_sub, coeff_ofNat_mul,
    coeff_one, coeff_X, coeff_X_pow, ite_eq_left, ite_eq_right] at h
  rw [show n + 14 - 1 = n + 13 by omega,
    show n + 14 - 2 = n + 12 by omega,
    show n + 14 - 3 = n + 11 by omega,
    show n + 14 - 4 = n + 10 by omega,
    show n + 14 - 5 = n + 9 by omega,
    show n + 14 - 6 = n + 8 by omega,
    show n + 14 - 7 = n + 7 by omega,
    show n + 14 - 8 = n + 6 by omega,
    show n + 14 - 9 = n + 5 by omega,
    show n + 14 - 10 = n + 4 by omega,
    show n + 14 - 11 = n + 3 by omega,
    show n + 14 - 12 = n + 2 by omega,
    show n + 14 - 13 = n + 1 by omega,
    show n + 14 - 14 = n by omega] at h
  linarith

theorem orbit_recurrence_fourteen (n : ℕ) :
    (a5 (n + 14) : ℤ) = 18 * (a5 (n + 13) : ℤ) - 63 * (a5 (n + 12) : ℤ) - 144 * (a5 (n + 11) : ℤ) + 1060 * (a5 (n + 10) : ℤ) - 1296 * (a5 (n + 9) : ℤ) - 1312 * (a5 (n + 8) : ℤ) + 3492 * (a5 (n + 7) : ℤ) - 1312 * (a5 (n + 6) : ℤ) - 1296 * (a5 (n + 5) : ℤ) + 1060 * (a5 (n + 4) : ℤ) - 144 * (a5 (n + 3) : ℤ) - 63 * (a5 (n + 2) : ℤ) + 18 * (a5 (n + 1) : ℤ) - (a5 n : ℤ) := by
  exact_mod_cast orbit_recurrence_fourteen_rat n

theorem orbit_initial_values :
    a5 0 = 1 ∧ a5 1 = 5 ∧ a5 2 = 33 ∧ a5 3 = 329 ∧ a5 4 = 3818 ∧ a5 5 = 46878 ∧ a5 6 = 584386 ∧ a5 7 = 7318152 ∧ a5 8 = 91752831 ∧ a5 9 = 1150774799 ∧ a5 10 = 14434490195 ∧ a5 11 = 181060839597 ∧ a5 12 = 2271175917429 ∧ a5 13 = 28489049801109 := by
  have h0 := orbit_coefficient_equation 0
  have h1 := orbit_coefficient_equation 1
  have h2 := orbit_coefficient_equation 2
  have h3 := orbit_coefficient_equation 3
  have h4 := orbit_coefficient_equation 4
  have h5 := orbit_coefficient_equation 5
  have h6 := orbit_coefficient_equation 6
  have h7 := orbit_coefficient_equation 7
  have h8 := orbit_coefficient_equation 8
  have h9 := orbit_coefficient_equation 9
  have h10 := orbit_coefficient_equation 10
  have h11 := orbit_coefficient_equation 11
  have h12 := orbit_coefficient_equation 12
  have h13 := orbit_coefficient_equation 13
  norm_num only [orbitLag, numeratorA, map_add, map_sub, coeff_ofNat_mul,
    coeff_one, coeff_X, coeff_X_pow, ite_true, ite_false] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have e0 : (a5 0 : ℚ) = 1 := by linarith only [h0]
  have e1 : (a5 1 : ℚ) = 5 := by linarith only [h1, e0]
  have e2 : (a5 2 : ℚ) = 33 := by linarith only [h2, e0, e1]
  have e3 : (a5 3 : ℚ) = 329 := by linarith only [h3, e0, e1, e2]
  have e4 : (a5 4 : ℚ) = 3818 := by linarith only [h4, e0, e1, e2, e3]
  have e5 : (a5 5 : ℚ) = 46878 := by linarith only [h5, e0, e1, e2, e3, e4]
  have e6 : (a5 6 : ℚ) = 584386 := by linarith only [h6, e0, e1, e2, e3, e4, e5]
  have e7 : (a5 7 : ℚ) = 7318152 := by linarith only [h7, e0, e1, e2, e3, e4, e5, e6]
  have e8 : (a5 8 : ℚ) = 91752831 := by linarith only [h8, e0, e1, e2, e3, e4, e5, e6, e7]
  have e9 : (a5 9 : ℚ) = 1150774799 := by linarith only [h9, e0, e1, e2, e3, e4, e5, e6, e7, e8]
  have e10 : (a5 10 : ℚ) = 14434490195 := by linarith only [h10, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  have e11 : (a5 11 : ℚ) = 181060839597 := by linarith only [h11, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  have e12 : (a5 12 : ℚ) = 2271175917429 := by linarith only [h12, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  have e13 : (a5 13 : ℚ) = 28489049801109 := by linarith only [h13, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]
  exact_mod_cast (show (a5 0 : ℚ) = 1 ∧ (a5 1 : ℚ) = 5 ∧ (a5 2 : ℚ) = 33 ∧ (a5 3 : ℚ) = 329 ∧ (a5 4 : ℚ) = 3818 ∧ (a5 5 : ℚ) = 46878 ∧ (a5 6 : ℚ) = 584386 ∧ (a5 7 : ℚ) = 7318152 ∧ (a5 8 : ℚ) = 91752831 ∧ (a5 9 : ℚ) = 1150774799 ∧ (a5 10 : ℚ) = 14434490195 ∧ (a5 11 : ℚ) = 181060839597 ∧ (a5 12 : ℚ) = 2271175917429 ∧ (a5 13 : ℚ) = 28489049801109 from
    ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩)

theorem orbit_recurrence_first : a5 14 = 357359559989069 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := orbit_initial_values
  have h := orbit_recurrence_fourteen 0
  norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13] at h
  exact_mod_cast h

theorem five_row_main_theorem :
    denominatorQ (X : PowerSeries ℚ) * orbitSeries = numeratorA X ∧
    orbitSeries = numeratorA X * (denominatorQ X)⁻¹ ∧
    (∀ n : ℕ, (a5 (n + 14) : ℤ) = 18 * (a5 (n + 13) : ℤ) - 63 * (a5 (n + 12) : ℤ) - 144 * (a5 (n + 11) : ℤ) + 1060 * (a5 (n + 10) : ℤ) - 1296 * (a5 (n + 9) : ℤ) - 1312 * (a5 (n + 8) : ℤ) + 3492 * (a5 (n + 7) : ℤ) - 1312 * (a5 (n + 6) : ℤ) - 1296 * (a5 (n + 5) : ℤ) + 1060 * (a5 (n + 4) : ℤ) - 144 * (a5 (n + 3) : ℤ) - 63 * (a5 (n + 2) : ℤ) + 18 * (a5 (n + 1) : ℤ) - (a5 n : ℤ)) ∧
    (a5 0 = 1 ∧ a5 1 = 5 ∧ a5 2 = 33 ∧ a5 3 = 329 ∧ a5 4 = 3818 ∧ a5 5 = 46878 ∧ a5 6 = 584386 ∧ a5 7 = 7318152 ∧ a5 8 = 91752831 ∧ a5 9 = 1150774799 ∧ a5 10 = 14434490195 ∧ a5 11 = 181060839597 ∧ a5 12 = 2271175917429 ∧ a5 13 = 28489049801109) :=
  ⟨orbit_series_identity, orbit_series_rational, orbit_recurrence_fourteen, orbit_initial_values⟩

end Domino.FiveRows
