module

public import Domino.Board.Partial

/-! 建模的非空实例与不可铺实例。它们不是三行递推或半棋盘双射的证明。 -/

@[expose] public section

namespace Domino

def singleEdgeTiling {m w : ℕ} (e : Edge m w) (h : e.val = Finset.univ) : Tiling m w :=
  ⟨{e}, by
    constructor
    · intro c
      simp [h]
    · intro e₁ h₁ e₂ h₂ _ _ _
      exact (Finset.mem_singleton.mp h₁).trans (Finset.mem_singleton.mp h₂).symm⟩

def horizontalUnitTiling : Tiling 1 2 :=
  singleEdgeTiling (edgeOfAdjacent (0, 0) (0, 1) (by decide)) (by decide)

def verticalUnitTiling : Tiling 2 1 :=
  singleEdgeTiling (edgeOfAdjacent (0, 0) (1, 0) (by decide)) (by decide)

theorem one_cell_not_tileable : ¬ Nonempty (Tiling 1 1) := by
  rintro ⟨T⟩
  obtain ⟨e, _, _⟩ := cover_exactly_one T (0, 0) (Finset.notMem_empty _)
  obtain ⟨a, b, h, _⟩ := e.property
  exact adjacent_ne h (Subsingleton.elim a b)

theorem diagonal_not_adjacent : ¬ Adjacent ((0, 0) : Cell 2 2) (1, 1) := by decide

end Domino
