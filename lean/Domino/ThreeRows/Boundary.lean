module

public import Domino.ThreeRows.OrbitCounts
public import Domino.HalfBoard.Examples

/-! 已接通实际轨道的少量边界推论；主生成函数和七阶递推仍在 M6。 -/

@[expose] public section

namespace Domino

theorem a_one : a 1 = 2 := by
  have h := orbit_odd 0
  norm_num [ordinary_eq_alpha, alpha, profilePair] at h
  exact h

theorem a_two : a 2 = 5 := by
  have h := orbit_even 1
  norm_num [ordinary_eq_alpha, alpha, profilePair] at h
  exact h

theorem three_row_small_orbit_counts : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 5 := ⟨a_zero, a_one, a_two⟩

theorem width_two_counts :
    ordinaryCount 3 1 = 3 ∧ fixedCount 3 1 horizontal = 1 ∧ fixedCount 3 1 vertical = 3 ∧
      fixedCount 3 1 halfTurn = 1 ∧ a 1 = 2 := by
  obtain ⟨hd, hh, hv, hr⟩ := three_row_width_two_fixed_counts
  exact ⟨hd, hh, hv, hr, a_one⟩

end Domino
