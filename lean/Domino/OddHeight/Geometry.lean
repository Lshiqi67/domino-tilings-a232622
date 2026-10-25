module

public import Domino.OddHeight.PathCompletion

/-! 路径补全的几何证书：左侧内部砖、跨中线砖及右侧对称像。 -/

@[expose] public section

namespace Domino.General

variable {m : ℕ}

theorem grid_left_agreement {n w : ℕ} {S U : State m}
    (R : GridMatching n S) (Q : GridMatching w U) (hnw : n ≤ w)
    (hh : ∀ k, k ≤ n → gridH R k = gridH Q k)
    (a b : (GridCell m)) (ha : a.2 < n) (hb : b.2 < n) : R.rel a b ↔ Q.rel a b := by
  have hv (k : ℕ) (hk : k < n) : gridV R k = gridV Q k := by
    apply column_cover_unique (gridH Q k) (gridH Q (k + 1))
    · simpa only [frameOfGrid, hh k (by omega), hh (k + 1) (by omega)] using
        (frameOfGrid R).column k hk
    · exact (frameOfGrid Q).column k (by omega)
  have hR := congrArg (fun G : GridMatching n S => G.rel a b) (grid_frame_roundtrip R)
  have hQ := congrArg (fun G : GridMatching w U => G.rel a b) (grid_frame_roundtrip Q)
  rw [← hR, ← hQ]
  change (a.2 < n ∧ b.2 < n ∧ GridLink (gridH R) (gridV R) a b) ↔
    (a.2 < w ∧ b.2 < w ∧ GridLink (gridH Q) (gridV Q) a b)
  simp only [ha, hb, show a.2 < w by omega, show b.2 < w by omega, true_and]
  simp only [GridLink, hh a.2 (by omega), hh (a.2 + 1) (by omega), hv a.2 ha]

theorem axial_restrict_state {b : Bool} {n : ℕ} (T : AxialFixed (m := m) b n) (k : ℕ) (hk : k ≤ n) :
    ((partialTilingEquivPath n ((axialFixedEquivPartial b n T).1.val))
      (axialFixedEquivPartial b n T).2).state k = (tilingPath T.val).state k := by
  let Q := restrictAxialPath (axialFixedEquivPath b n T)
  have h := congrArg (fun A : StatePath n Q.1.val => A.state k)
    ((partialTilingEquivPath n Q.1.val).apply_symm_apply Q.2)
  exact h.trans (by
    change (if k ≤ n then (tilingPath T.val).state k else ∅) = _
    simp [hk])

theorem axial_restrict_terminal {b : Bool} {n : ℕ} (T : AxialFixed (m := m) b n) :
    (axialFixedEquivPartial b n T).1.val = (tilingPath T.val).state n := rfl

def leftCell {n : ℕ} (a : Cell m n) : Cell m (2 * n) :=
  (a.1, ⟨a.2.val, by have := a.2.isLt; omega⟩)

theorem axial_restrict_internal {b : Bool} {n : ℕ} (T : AxialFixed (m := m) b n) (a c : Cell m n) :
    (a, c) ∈ coverBonds (axialFixedEquivPartial b n T).2.val ↔
      (leftCell a, leftCell c) ∈ coverBonds T.val := by
  let P := (axialFixedEquivPartial b n T).2
  let U := (partialEmptyEquivTiling m (2 * n)).symm T.val
  have hh (k : ℕ) (hk : k ≤ n) : gridH (gridOfPartial P) k = gridH (gridOfPartial U) k :=
    axial_restrict_state T k hk
  have h := grid_left_agreement (gridOfPartial P) (gridOfPartial U) (by omega) hh
    (gridCell a) (gridCell c) a.2.isLt c.2.isLt
  change (gridOfPartial P).rel (gridCell a) (gridCell c) ↔
    (gridOfPartial U).rel (gridCell (leftCell a)) (gridCell (leftCell c)) at h
  simpa [gridOfPartial_at, P, U, partialEmptyEquivTiling, coverBonds] using h

theorem axial_complete_internal {b : Bool} {n : ℕ} (P : HalfPartial (m := m) b n) (a c : Cell m n) :
    (leftCell a, leftCell c) ∈ coverBonds ((axialFixedEquivPartial b n).symm P).val ↔
      (a, c) ∈ coverBonds P.2.val := by
  have h := axial_restrict_internal ((axialFixedEquivPartial b n).symm P) a c
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem axial_complete_terminal {b : Bool} {n : ℕ} (P : HalfPartial (m := m) b n) :
    (tilingPath ((axialFixedEquivPartial b n).symm P).val).state n = P.1.val := by
  have h := axial_restrict_terminal ((axialFixedEquivPartial b n).symm P)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem axial_complete_crossing {b : Bool} {n : ℕ} (P : HalfPartial (m := m) b n) (hn : 0 < n)
    (r : Fin m) :
    ((r, ⟨n - 1, by omega⟩), (r, ⟨n, by omega⟩)) ∈
      coverBonds ((axialFixedEquivPartial b n).symm P).val ↔ r ∈ P.1.val := by
  rw [← tilingPath_cut _ n hn (by omega), axial_complete_terminal]

theorem axial_complete_right {b : Bool} {n : ℕ} (P : HalfPartial (m := m) b n) (a c : Cell m n) :
    (cellAction (axialSymmetry b) (leftCell a), cellAction (axialSymmetry b) (leftCell c)) ∈
      coverBonds ((axialFixedEquivPartial b n).symm P).val ↔
      (a, c) ∈ coverBonds P.2.val := by
  let T := (axialFixedEquivPartial b n).symm P
  rw [← coverBonds_action, T.property]
  exact axial_complete_internal P a c

theorem crossing_bond_same_row {n : ℕ} (T : Tiling m (2 * n)) (a c : Cell m (2 * n))
    (h : (a, c) ∈ coverBonds T) (ha : a.2.val < n) (hc : n ≤ c.2.val) :
    a.1 = c.1 ∧ a.2.val + 1 = n ∧ c.2.val = n := by
  rcases (coverBonds_valid T).1 a c h with ⟨hr, hcol⟩ | ⟨hcol, _⟩
  · exact ⟨hr, by omega, by omega⟩
  · have := congrArg Fin.val hcol
    omega

end Domino.General
