module

public import Domino.HalfBoard.Reflection

/-! B03：半周补全只要求终端行集合反转不变，不要求左半铺法自身对称。 -/

@[expose] public section

namespace Domino

abbrev SymmetricTerminal := {S : State 3 // reverseState S = S}

noncomputable def halfTurnFixedEquivPartial (n : ℕ) :
    {T : Tiling 3 (2 * n) // halfTurn • T = T} ≃
      (Σ S : SymmetricTerminal, PartialTiling 3 n S.val) := axialFixedEquivPartial true n

noncomputable def completeHalfTurn {n : ℕ} (P : Σ S : SymmetricTerminal, PartialTiling 3 n S.val) :=
  (halfTurnFixedEquivPartial n).symm P

noncomputable def restrictHalfTurn {n : ℕ} (T : {T : Tiling 3 (2 * n) // halfTurn • T = T}) :=
  halfTurnFixedEquivPartial n T

theorem restrict_complete_halfTurn {n : ℕ} (P : Σ S : SymmetricTerminal, PartialTiling 3 n S.val) :
    restrictHalfTurn (completeHalfTurn P) = P :=
  (halfTurnFixedEquivPartial n).apply_symm_apply P

theorem complete_restrict_halfTurn {n : ℕ} (T : {T : Tiling 3 (2 * n) // halfTurn • T = T}) :
    completeHalfTurn (restrictHalfTurn T) = T :=
  (halfTurnFixedEquivPartial n).symm_apply_apply T

theorem halfTurn_terminal_necessary {n : ℕ} (T : {T : Tiling 3 (2 * n) // halfTurn • T = T}) :
    reverseState ((tilingPath T.val).state n) = (tilingPath T.val).state n :=
  (axialFixedEquivPartial true n T).1.property

theorem halfTurn_extension_iff {n : ℕ} {S : State 3} (P : PartialTiling 3 n S) :
    (∃ T : {T : Tiling 3 (2 * n) // halfTurn • T = T},
      ∀ k, k ≤ n → (partialTilingEquivPath n S P).state k = (tilingPath T.val).state k) ↔
      reverseState S = S := by
  constructor
  · rintro ⟨T, h⟩
    have he : S = (tilingPath T.val).state n := (partialTilingEquivPath n S P).finish.symm.trans
      (h n (by omega))
    rw [he]
    exact halfTurn_terminal_necessary T
  · intro hS
    let Q : HalfPartial true n := ⟨⟨S, hS⟩, P⟩
    refine ⟨(axialFixedEquivPartial true n).symm Q, ?_⟩
    intro k hk
    have h := axial_restrict_state ((axialFixedEquivPartial true n).symm Q) k hk
    rw [Equiv.apply_symm_apply] at h
    exact h

theorem halfTurn_fixed_count (n : ℕ) :
    fixedCount 3 n halfTurn = ∑ S : SymmetricTerminal, profileCount n S.val := by
  classical
  exact (Fintype.card_congr (halfTurnFixedEquivPartial n)).trans Fintype.card_sigma

end Domino
