module

public import Domino.ThreeRows.Series

/-! T02：真实三行铺法轨道的主生成函数。 -/

@[expose] public section

namespace Domino

open PowerSeries

theorem burnside_series_identity :
    4 * orbitSeries = ordinarySeries + horizontalSeries + verticalSeries + halfTurnSeries := by
  ext n
  simp only [coeff_ofNat_mul, map_add, coeff_orbitSeries, ordinarySeries,
    horizontalSeries, verticalSeries, halfTurnSeries, coeff_countSeries]
  exact_mod_cast four_mul_orbitCount 3 n

theorem orbit_series_identity : orbitDenom * orbitSeries = orbitNumerator := by
  have h : 4 * (orbitDenom * orbitSeries) = 4 * orbitNumerator := by
    unfold orbitDenom
    linear_combination
      (1 - X) * ordinaryDenom * parityDenom * burnside_series_identity +
      (1 - X) * parityDenom * ordinary_series_identity +
      ordinaryDenom * parityDenom * horizontal_series_identity +
      (1 - X) * ordinaryDenom * vertical_series_identity +
      (1 - X) * ordinaryDenom * halfTurn_series_identity + common_numerator_identity
  ext n
  have hc := congrArg (coeff n) h
  simp only [coeff_ofNat_mul] at hc
  linarith

theorem orbit_series_rational : orbitSeries = orbitNumerator * orbitDenom⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by simp : constantCoeff orbitDenom ≠ 0)).2
  simpa only [mul_comm] using orbit_series_identity

theorem orbit_series_paper :
    orbitSeries = (-1 + 3 * X + 4 * X ^ 2 - 10 * X ^ 3 + 4 * X ^ 5 - X ^ 6) *
      ((X - 1) * (X ^ 2 - 4 * X + 1) * (X ^ 4 - 4 * X ^ 2 + 1))⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by simp :
    constantCoeff ((X - 1) * (X ^ 2 - 4 * X + 1) * (X ^ 4 - 4 * X ^ 2 + 1) : PowerSeries ℚ) ≠ 0)).2
  have h := orbit_series_identity
  unfold orbitDenom ordinaryDenom parityDenom orbitNumerator at h
  linear_combination -h

end Domino
