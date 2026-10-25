module

public import Domino.HalfBoard.HalfTurn

/-! B04：三行上下反射固定铺法排除所有竖砖，且全水平铺法唯一。 -/

@[expose] public section

namespace Domino

theorem horizontal_fixed_no_vertical {w : ℕ} (T : Tiling 3 w) (hT : horizontal • T = T)
    (a c : Cell 3 w) (h : (a, c) ∈ coverBonds T) : a.1 = c.1 := by
  have hh : (cellAction horizontal a, cellAction horizontal c) ∈ coverBonds T := by
    apply (coverBonds_action horizontal T a c).mp
    simpa [hT] using h
  have adj := (coverBonds_valid T).1 a c h
  rcases a with ⟨r, i⟩
  rcases c with ⟨s, j⟩
  rcases adj with ⟨hr, _⟩ | ⟨hc, hr⟩
  · exact hr
  · dsimp only at hc hr
    subst j
    have hs := (coverBonds_valid T).2.1 _ _ h
    have hhs := (coverBonds_valid T).2.1 _ _ hh
    change ((r.rev, i), (s.rev, i)) ∈ coverBonds T at hh
    change ((s.rev, i), (r.rev, i)) ∈ coverBonds T at hhs
    fin_cases r <;> fin_cases s <;> norm_num at hr
    all_goals
      first
      | have he := (coverBonds_valid T).2.2.2 _ _ _ hs hhs
        have := congrArg (fun x : Cell 3 w => x.1.val) he
        norm_num at this
      | have he := (coverBonds_valid T).2.2.2 _ _ _ h hh
        have := congrArg (fun x : Cell 3 w => x.1.val) he
        norm_num at this

def horizontalProfile (k : ℕ) : State 3 := if k % 2 = 0 then ∅ else Finset.univ

@[simp] theorem horizontalProfile_zero : horizontalProfile 0 = ∅ := rfl

theorem horizontalProfile_values (k : ℕ) :
    horizontalProfile k = ∅ ∨ horizontalProfile k = Finset.univ := by
  unfold horizontalProfile
  split_ifs <;> simp

theorem horizontalProfile_succ (k : ℕ) :
    horizontalProfile (k + 1) = Finset.univ \ horizontalProfile k := by
  have hk := Nat.mod_lt k (by decide : 0 < 2)
  have hs := Nat.mod_lt (k + 1) (by decide : 0 < 2)
  by_cases he : k % 2 = 0
  · have ho : (k + 1) % 2 ≠ 0 := by omega
    simp [horizontalProfile, he, ho]
  · have hz : (k + 1) % 2 = 0 := by omega
    simp [horizontalProfile, he, hz]

theorem horizontalProfile_step (k : ℕ) : Legal3 (horizontalProfile k) (horizontalProfile (k + 1)) := by
  rw [horizontalProfile_succ]
  rcases horizontalProfile_values k with h | h <;> rw [h] <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem horizontal_next_unique : ∀ p q : State 3,
    (p = ∅ ∨ p = Finset.univ) → reverseState q = q → Legal3 p q → q = Finset.univ \ p := by decide

theorem horizontalProfile_reverse (k : ℕ) : reverseState (horizontalProfile k) = horizontalProfile k := by
  rcases horizontalProfile_values k with h | h <;> rw [h] <;> decide

theorem horizontal_fixed_path_state {w : ℕ} (T : Tiling 3 w) (hT : horizontal • T = T)
    (k : ℕ) (hk : k ≤ w) : (tilingPath T).state k = horizontalProfile k := by
  induction k with
  | zero => exact (tilingPath T).start
  | succ k ih =>
      have hp := ih (by omega)
      have hs := (tilingPath T).step k (by omega)
      rw [hp] at hs
      rw [horizontalProfile_succ]
      exact horizontal_next_unique _ _ (horizontalProfile_values k)
        ((horizontal_fixed_iff_path T).mp hT (k + 1)) hs

def allHorizontalPath (n : ℕ) : StatePath (2 * n) ∅ where
  state k := if k ≤ 2 * n then horizontalProfile k else ∅
  start := by simp
  finish := by simp [horizontalProfile]
  support k hk := by simp [show ¬k ≤ 2 * n by omega]
  step k hk := by
    simpa [show k ≤ 2 * n by omega, show k + 1 ≤ 2 * n by omega] using horizontalProfile_step k

noncomputable def allHorizontalTiling (n : ℕ) : Tiling 3 (2 * n) :=
  (tilingEquivClosedPath (2 * n)).symm (allHorizontalPath n)

theorem allHorizontalTiling_fixed (n : ℕ) : horizontal • allHorizontalTiling n = allHorizontalTiling n := by
  apply (horizontal_fixed_iff_path _).mpr
  intro k
  simp only [tilingPath, allHorizontalTiling, Equiv.apply_symm_apply, allHorizontalPath]
  split_ifs
  · exact horizontalProfile_reverse k
  · exact reverseState_empty 3

theorem horizontal_fixed_unique (n : ℕ) (T : Tiling 3 (2 * n)) (hT : horizontal • T = T) :
    T = allHorizontalTiling n := by
  apply (tilingEquivClosedPath (2 * n)).injective
  apply statePath_ext
  funext k
  change (tilingPath T).state k = ((tilingEquivClosedPath (2 * n)) (allHorizontalTiling n)).state k
  simp only [allHorizontalTiling, Equiv.apply_symm_apply, allHorizontalPath]
  by_cases hk : k ≤ 2 * n
  · simpa [hk] using horizontal_fixed_path_state T hT k hk
  · simp [hk, (tilingPath T).support k (by omega)]

theorem horizontal_fixed_card_three (n : ℕ) : fixedCount 3 n horizontal = 1 := by
  classical
  let _ : Unique {T : Tiling 3 (2 * n) // horizontal • T = T} :=
    { default := ⟨allHorizontalTiling n, allHorizontalTiling_fixed n⟩
      uniq := fun T => Subtype.ext (horizontal_fixed_unique n T.val T.property) }
  exact Fintype.card_unique

end Domino
