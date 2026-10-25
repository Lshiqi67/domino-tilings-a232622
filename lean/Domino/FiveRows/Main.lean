module

public import Domino.FiveRows.Series

/-! 五行真实铺法轨道的显式有理生成函数。 -/

@[expose] public section

namespace Domino.FiveRows

open PowerSeries

noncomputable abbrev a5 (n : ℕ) : ℕ := orbitCount 5 n

noncomputable def orbitSeries : PowerSeries ℚ := countSeries a5

def denominatorQ {R : Type*} [Ring R] (t : R) : R :=
  denominatorH t * denominatorP t * denominatorP (t ^ 2)

def numeratorA {R : Type*} [Ring R] (t : R) : R :=
  1 - 13 * t + 6 * t ^ 2 + 194 * t ^ 3 - 365 * t ^ 4 - 371 * t ^ 5 +
    1304 * t ^ 6 - 594 * t ^ 7 - 703 * t ^ 8 + 717 * t ^ 9 -
    154 * t ^ 10 - 36 * t ^ 11 + 15 * t ^ 12 - t ^ 13

theorem denominator_expanded {R : Type*} [CommRing R] (t : R) :
    denominatorQ t = 1 - 18 * t + 63 * t ^ 2 + 144 * t ^ 3 - 1060 * t ^ 4 +
      1296 * t ^ 5 + 1312 * t ^ 6 - 3492 * t ^ 7 + 1312 * t ^ 8 +
      1296 * t ^ 9 - 1060 * t ^ 10 + 144 * t ^ 11 + 63 * t ^ 12 - 18 * t ^ 13 + t ^ 14 := by
  unfold denominatorQ denominatorH denominatorP
  ring

theorem common_numerator_identity {R : Type*} [CommRing R] (t : R) :
    denominatorH t * denominatorP (t ^ 2) * numeratorColumn t 0 +
      denominatorP t * denominatorP (t ^ 2) * (1 - t) +
      denominatorH t * denominatorP t * numeratorV t +
      denominatorH t * denominatorP t * numeratorR t = 4 * numeratorA t := by
  simp only [denominatorH, denominatorP, numeratorColumn, numeratorV, numeratorR,
    numeratorA, Matrix.cons_val_zero]
  ring

@[simp] theorem denominator_constant : constantCoeff (denominatorQ (X : PowerSeries ℚ)) = 1 := by
  simp [denominatorQ, denominatorH, denominatorP]

theorem denominator_isUnit : IsUnit (denominatorQ (X : PowerSeries ℚ)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

theorem burnside_series_identity :
    4 * orbitSeries = ordinarySeries + horizontalSeries + verticalSeries + halfTurnSeries := by
  ext n
  simp only [coeff_ofNat_mul, map_add, orbitSeries, ordinarySeries, horizontalSeries,
    verticalSeries, halfTurnSeries, coeff_countSeries, a5]
  exact_mod_cast four_mul_orbitCount 5 n

theorem orbit_series_identity : denominatorQ (X : PowerSeries ℚ) * orbitSeries = numeratorA X := by
  have h : 4 * (denominatorQ (X : PowerSeries ℚ) * orbitSeries) = 4 * numeratorA X := by
    unfold denominatorQ
    have hc := common_numerator_identity (X : PowerSeries ℚ)
    simp only [numeratorColumn, Matrix.cons_val_zero] at hc
    linear_combination
      denominatorH X * denominatorP X * denominatorP (X ^ 2) * burnside_series_identity +
      denominatorH X * denominatorP (X ^ 2) * ordinary_series_identity +
      denominatorP X * denominatorP (X ^ 2) * horizontal_series_identity +
      denominatorH X * denominatorP X * vertical_series_identity +
      denominatorH X * denominatorP X * halfTurn_series_identity + hc
  ext n
  have hc := congrArg (coeff n) h
  simp only [coeff_ofNat_mul] at hc
  linarith

theorem orbit_series_rational :
    orbitSeries = numeratorA (X : PowerSeries ℚ) * (denominatorQ X)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by simp : constantCoeff (denominatorQ (X : PowerSeries ℚ)) ≠ 0)).2
  simpa only [mul_comm] using orbit_series_identity

end Domino.FiveRows
