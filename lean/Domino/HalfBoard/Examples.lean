module

public import Domino.HalfBoard.Horizontal
public import Domino.Transfer.Examples

/-! 三类固定点接口的零宽和 3×2 边界；不调用 Burnside。 -/

@[expose] public section

namespace Domino

theorem halfPartial_zero_terminal (b : Bool) (P : HalfPartial b 0) : P.1.val = ∅ :=
  partial_width_zero_state P.2

theorem three_row_empty_fixed_counts :
    fixedCount 3 0 horizontal = 1 ∧ fixedCount 3 0 vertical = 1 ∧ fixedCount 3 0 halfTurn = 1 := by
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem three_row_width_two_fixed_counts :
    ordinaryCount 3 1 = 3 ∧ fixedCount 3 1 horizontal = 1 ∧
      fixedCount 3 1 vertical = 3 ∧ fixedCount 3 1 halfTurn = 1 := by
  refine ⟨?_, horizontal_fixed_card_three 1, ?_, ?_⟩
  · rw [ordinary_count_profile, profile_count_eval]
    decide
  · rw [reflection_fixed_count]
    simp only [profile_count_eval]
    decide
  · rw [halfTurn_fixed_count]
    simp only [profile_count_eval]
    decide

end Domino
