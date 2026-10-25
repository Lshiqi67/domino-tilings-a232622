module

public import Domino.OddHeight.Geometry
public import Domino.OddHeight.OddReflection

@[expose] public section

namespace Domino.General

theorem odd_restrict_state {m n : ℕ} (h0 : Legal (∅ : State m) ∅)
    (T : {T : Tiling m (2 * n + 1) // vertical • T = T}) (k : ℕ) (hk : k ≤ n) :
    (tilingPath (oddReflectionFixedEquiv h0 n T)).state k = (tilingPath T.val).state k := by
  let Q : OddAxialPath m n := ⟨tilingPath T.val, (axial_fixed_iff_path false T.val).mp T.property⟩
  have h := congrArg (fun P : StatePath (m := m) n ∅ => P.state k)
    ((tilingEquivClosedPath (m := m) n).apply_symm_apply (restrictOddPath Q))
  exact h.trans (by simp [restrictOddPath, Q, hk])

def oddLeftCell {m n : ℕ} (a : Cell m n) : Cell m (2 * n + 1) :=
  (a.1, ⟨a.2.val, by have := a.2.isLt; omega⟩)

theorem odd_restrict_internal {m n : ℕ} (h0 : Legal (∅ : State m) ∅)
    (T : {T : Tiling m (2 * n + 1) // vertical • T = T}) (a c : Cell m n) :
    (a, c) ∈ coverBonds (oddReflectionFixedEquiv h0 n T) ↔
      (oddLeftCell a, oddLeftCell c) ∈ coverBonds T.val := by
  let P := (partialEmptyEquivTiling m n).symm (oddReflectionFixedEquiv h0 n T)
  let U := (partialEmptyEquivTiling m (2 * n + 1)).symm T.val
  have hh (k : ℕ) (hk : k ≤ n) : gridH (gridOfPartial P) k = gridH (gridOfPartial U) k :=
    odd_restrict_state h0 T k hk
  have h := grid_left_agreement (gridOfPartial P) (gridOfPartial U) (by omega) hh
    (gridCell a) (gridCell c) a.2.isLt c.2.isLt
  change (gridOfPartial P).rel (gridCell a) (gridCell c) ↔
    (gridOfPartial U).rel (gridCell (oddLeftCell a)) (gridCell (oddLeftCell c)) at h
  simpa [gridOfPartial_at, P, U, partialEmptyEquivTiling, coverBonds] using h

def topCell {k n : ℕ} (a : Cell k (2 * n)) : Cell (2 * k + 1) (2 * n) :=
  (⟨a.1.val, by have := a.1.isLt; omega⟩, a.2)

theorem horizontal_restrict_top_bonds {k n : ℕ}
    (T : {T : Tiling (2 * k + 1) (2 * n) // horizontal • T = T}) (a c : Cell k (2 * n)) :
    (a, c) ∈ coverBonds (horizontalFixedEquivTop k n T) ↔
      (topCell a, topCell c) ∈ coverBonds T.val := by
  change (a, c) ∈ coverBonds (transposeTiling
    (oddReflectionFixedEquiv (legal_empty_even n) k (horizontalFixedTransposeEquiv _ _ T))) ↔ _
  rw [transposeTiling_bonds, mem_transposeBonds, odd_restrict_internal]
  change (oddLeftCell (a.2, a.1), oddLeftCell (c.2, c.1)) ∈ coverBonds (transposeTiling T.val) ↔ _
  rw [transposeTiling_bonds, mem_transposeBonds]
  rfl

theorem horizontal_complete_top_bonds {k n : ℕ} (P : Tiling k (2 * n)) (a c : Cell k (2 * n)) :
    (topCell a, topCell c) ∈ coverBonds ((horizontalFixedEquivTop k n).symm P).val ↔
      (a, c) ∈ coverBonds P := by
  have h := horizontal_restrict_top_bonds ((horizontalFixedEquivTop k n).symm P) a c
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end Domino.General
