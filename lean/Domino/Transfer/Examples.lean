module

public import Domino.Transfer.Count

/-! 有限局部表与少量边界推论；一般宽度结论来自双射及递推证明。 -/

@[expose] public section

namespace Domino

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem legal3_transition_card :
    Fintype.card {pq : State 3 × State 3 // Legal3 pq.1 pq.2} = 12 := by decide

def profileEval : ℕ → State 3 → ℕ
  | 0, S => if S = ∅ then 1 else 0
  | w + 1, S => ∑ p : State 3, profileEval w p * transfer3 p S

theorem profile_count_eval (w : ℕ) (S : State 3) : profileCount w S = profileEval w S := by
  induction w generalizing S with
  | zero => exact profile_count_zero S
  | succ w ih =>
      rw [profile_count_succ]
      simp only [profileEval, ih]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem profile_width_one : ∀ S : State 3,
    profileCount 1 S = if S = {0} ∨ S = {2} ∨ S = Finset.univ then 1 else 0 := by
  intro S
  rw [profile_count_eval]
  have h : ∀ S : State 3,
      profileEval 1 S = if S = {0} ∨ S = {2} ∨ S = Finset.univ then 1 else 0 := by decide
  exact h S

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem three_row_small_tiling_counts :
    Fintype.card (Tiling 3 0) = 1 ∧ Fintype.card (Tiling 3 1) = 0 ∧
    Fintype.card (Tiling 3 2) = 3 ∧ Fintype.card (Tiling 3 3) = 0 ∧
    Fintype.card (Tiling 3 4) = 11 := by
  have h (w : ℕ) : Fintype.card (Tiling 3 w) = profileEval w ∅ :=
    (partial_empty_card 3 w).symm.trans (profile_count_eval w ∅)
  simp only [h]
  decide

end Domino
