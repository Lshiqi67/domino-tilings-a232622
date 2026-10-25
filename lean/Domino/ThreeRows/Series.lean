module

public import Domino.ThreeRows.Algebra
public import Domino.ThreeRows.OrbitCounts

/-! B08：从真实计数定义系数级数，证明四类固定点的分母恒等式。 -/

@[expose] public section

namespace Domino

open PowerSeries

noncomputable def ordinarySeries : PowerSeries ℚ := countSeries (ordinaryCount 3)
noncomputable def ordinaryShiftSeries : PowerSeries ℚ := countSeries fun n => ordinaryCount 3 (n + 1)
noncomputable def horizontalSeries : PowerSeries ℚ := countSeries fun n => fixedCount 3 n horizontal
noncomputable def verticalSeries : PowerSeries ℚ := countSeries fun n => fixedCount 3 n vertical
noncomputable def halfTurnSeries : PowerSeries ℚ := countSeries fun n => fixedCount 3 n halfTurn
noncomputable def orbitSeries : PowerSeries ℚ := countSeries a

@[simp] theorem coeff_orbitSeries (n : ℕ) : coeff n orbitSeries = (a n : ℚ) := coeff_countSeries _ _

theorem ordinary_series_identity : ordinaryDenom * ordinarySeries = 1 - X := by
  have h (n : ℕ) : (ordinaryCount 3 (n + 2) : ℚ) + ordinaryCount 3 n =
      4 * (ordinaryCount 3 (n + 1) : ℚ) := by exact_mod_cast ordinary_recurrence_add n
  convert series_second_order (fun n => (ordinaryCount 3 n : ℚ)) h using 1 <;>
    norm_num [ordinaryDenom, ordinarySeries, countSeries, ordinary_eq_alpha, alpha, profilePair,
      sub_eq_add_neg]

theorem ordinary_shift_identity : X * ordinaryShiftSeries = ordinarySeries - 1 := by
  simpa [ordinaryShiftSeries, ordinarySeries, countSeries] using
    series_shift (fun n => (ordinaryCount 3 n : ℚ))

theorem ordinary_shift_series_identity : ordinaryDenom * ordinaryShiftSeries = 3 - X := by
  apply X_mul_cancel
  calc
    X * (ordinaryDenom * ordinaryShiftSeries) = ordinaryDenom * (X * ordinaryShiftSeries) := by ring
    _ = ordinaryDenom * (ordinarySeries - 1) := by rw [ordinary_shift_identity]
    _ = (1 - X) - ordinaryDenom := by rw [mul_sub, ordinary_series_identity, mul_one]
    _ = X * (3 - X) := by unfold ordinaryDenom; ring

theorem even_ordinary_series_identity : parityDenom * doubleSeries ordinarySeries = 1 - X ^ 2 := by
  have h := congrArg doubleSeries ordinary_series_identity
  simp only [map_mul, map_sub, map_one] at h
  rw [double_ordinaryDenom] at h
  simpa only [doubleSeries, expand_X] using h

theorem even_shift_series_identity : parityDenom * doubleSeries ordinaryShiftSeries = 3 - X ^ 2 := by
  have h := congrArg doubleSeries ordinary_shift_series_identity
  simp only [map_mul, map_sub, map_ofNat] at h
  rw [double_ordinaryDenom] at h
  simpa only [doubleSeries, expand_X] using h

theorem even_shift_identity : X ^ 2 * doubleSeries ordinaryShiftSeries = doubleSeries ordinarySeries - 1 := by
  have h := congrArg doubleSeries ordinary_shift_identity
  simpa [map_mul, map_sub, doubleSeries] using h

theorem horizontal_series_identity : (1 - X) * horizontalSeries = 1 := by
  ext n
  cases n with
  | zero => simp [horizontalSeries, countSeries, sub_mul]
  | succ n => simp [horizontalSeries, sub_mul, coeff_succ_X_mul, horizontal_fixed_card_three, coeff_one]

theorem halfTurn_series_parity :
    halfTurnSeries = doubleSeries ordinarySeries + X * doubleSeries ordinarySeries := by
  apply series_ext_parity <;> intro j
  · simp [halfTurnSeries, ordinarySeries, halfTurn_even]
  · simp [halfTurnSeries, ordinarySeries, halfTurn_odd]

theorem vertical_series_parity_add :
    verticalSeries + 2 * doubleSeries ordinarySeries =
      doubleSeries ordinaryShiftSeries + X * doubleSeries ordinaryShiftSeries := by
  apply series_ext_parity <;> intro j
  · simp only [map_add, coeff_ofNat_mul, coeff_doubleSeries_even, coeff_X_doubleSeries_even,
      verticalSeries, ordinarySeries, ordinaryShiftSeries, coeff_countSeries, add_zero]
    exact_mod_cast reflection_even_add j
  · simp [verticalSeries, ordinaryShiftSeries, reflection_odd]

theorem halfTurn_series_identity :
    parityDenom * halfTurnSeries = 1 + X - X ^ 2 - X ^ 3 := by
  rw [halfTurn_series_parity]
  calc
    parityDenom * (doubleSeries ordinarySeries + X * doubleSeries ordinarySeries) =
        (1 + X) * (parityDenom * doubleSeries ordinarySeries) := by ring
    _ = (1 + X) * (1 - X ^ 2) := by rw [even_ordinary_series_identity]
    _ = _ := by ring

theorem vertical_series_identity :
    parityDenom * verticalSeries = 1 + 3 * X + X ^ 2 - X ^ 3 := by
  have h := congrArg (parityDenom * ·) vertical_series_parity_add
  have he := even_ordinary_series_identity
  have hs := even_shift_series_identity
  linear_combination h - 2 * he + (1 + X) * hs

theorem fixed_series_identities :
    (1 - X) * horizontalSeries = 1 ∧
    parityDenom * verticalSeries = 1 + 3 * X + X ^ 2 - X ^ 3 ∧
    parityDenom * halfTurnSeries = 1 + X - X ^ 2 - X ^ 3 :=
  ⟨horizontal_series_identity, vertical_series_identity, halfTurn_series_identity⟩

end Domino
