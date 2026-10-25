module

public import Domino.Series.Basic

/-! C03：只依赖环运算的通分恒等式；不使用计数或主定理。 -/

@[expose] public section

namespace Domino

open PowerSeries

noncomputable def ordinaryDenom : PowerSeries ℚ := 1 - 4 * X + X ^ 2
noncomputable def parityDenom : PowerSeries ℚ := 1 - 4 * X ^ 2 + X ^ 4
noncomputable def orbitDenom : PowerSeries ℚ := (1 - X) * ordinaryDenom * parityDenom
noncomputable def orbitNumerator : PowerSeries ℚ :=
  1 - 3 * X - 4 * X ^ 2 + 10 * X ^ 3 - 4 * X ^ 5 + X ^ 6

theorem double_ordinaryDenom : doubleSeries ordinaryDenom = parityDenom := by
  norm_num [doubleSeries, ordinaryDenom, parityDenom, map_sub, map_add, map_mul, map_pow,
    map_ofNat, ← pow_mul]

theorem orbitDenom_expanded :
    orbitDenom = 1 - 5 * X + X ^ 2 + 19 * X ^ 3 - 19 * X ^ 4 - X ^ 5 + 5 * X ^ 6 - X ^ 7 := by
  unfold orbitDenom ordinaryDenom parityDenom
  ring

theorem common_numerator_identity :
    (1 - X) * parityDenom * (1 - X) + ordinaryDenom * parityDenom +
      (1 - X) * ordinaryDenom * (1 + 3 * X + X ^ 2 - X ^ 3) +
      (1 - X) * ordinaryDenom * (1 + X - X ^ 2 - X ^ 3) = 4 * orbitNumerator := by
  unfold ordinaryDenom parityDenom orbitNumerator
  ring

@[simp] theorem orbitDenom_constant : constantCoeff orbitDenom = 1 := by
  simp [orbitDenom, ordinaryDenom, parityDenom]

theorem orbitDenom_isUnit : IsUnit orbitDenom := by
  rw [isUnit_iff_constantCoeff, orbitDenom_constant]
  exact isUnit_one

end Domino
