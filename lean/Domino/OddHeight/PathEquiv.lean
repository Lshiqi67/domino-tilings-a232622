module

public import Domino.OddHeight.Frame

/-! 合法路径只记录切口行集合。支持界使自然数索引与有限长度路径完全等价。 -/

@[expose] public section

namespace Domino.General

variable {m : ℕ}

structure StatePath (w : ℕ) (S : State m) where
  state : ℕ → State m
  start : state 0 = ∅
  finish : state w = S
  support : ∀ k, w < k → state k = ∅
  step : ∀ k, k < w → Legal (state k) (state (k + 1))

@[ext] theorem statePath_ext {w : ℕ} {S : State m} (P Q : StatePath w S)
    (h : P.state = Q.state) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

def pathCode {w : ℕ} {S : State m} (P : StatePath w S) : Fin (w + 1) → State m :=
  fun k => P.state k.val

theorem pathCode_injective (w : ℕ) (S : State m) :
    Function.Injective (@pathCode m w S) := by
  intro P Q h
  apply statePath_ext
  funext k
  by_cases hk : k ≤ w
  · exact congrFun h ⟨k, by omega⟩
  · rw [P.support k (by omega), Q.support k (by omega)]

instance statePathFinite (w : ℕ) (S : State m) : Finite (StatePath w S) :=
  Finite.of_injective pathCode (pathCode_injective w S)

noncomputable instance statePathFintype (w : ℕ) (S : State m) : Fintype (StatePath w S) :=
  Fintype.ofFinite _

def pathOfFrame {w : ℕ} {S : State m} (F : ColumnFrame w S) : StatePath w S where
  state := F.horizontal
  start := F.start
  finish := F.finish
  support := F.hsupport
  step k hk := (legal_iff_column_cover _ _).mpr ⟨F.vertical k, F.column k hk⟩

noncomputable def frameOfPath {w : ℕ} {S : State m} (P : StatePath w S) : ColumnFrame w S where
  horizontal := P.state
  vertical k := if hk : k < w then (fillColumn _ _ (P.step k hk)).val else ∅
  start := P.start
  finish := P.finish
  hsupport := P.support
  vsupport k hk := dite_eq_right (by omega)
  column k hk := by
    simp only [dite_eq_left hk]
    exact (fillColumn _ _ (P.step k hk)).property

noncomputable def frameEquivPath (w : ℕ) (S : State m) : ColumnFrame w S ≃ StatePath w S where
  toFun := pathOfFrame
  invFun := frameOfPath
  left_inv F := by
    apply columnFrame_ext
    · rfl
    · funext k
      by_cases hk : k < w
      · apply column_cover_unique (F.horizontal k) (F.horizontal (k + 1))
        · exact (frameOfPath (pathOfFrame F)).column k hk
        · exact F.column k hk
      · change (if h : k < w then _ else ∅) = F.vertical k
        rw [dite_eq_right hk, F.vsupport k (by omega)]
  right_inv P := statePath_ext _ _ rfl

noncomputable def partialTilingEquivPath (w : ℕ) (S : State m) :
    PartialTiling m w S ≃ StatePath w S :=
  (partialEquivFrame w S).trans (frameEquivPath w S)

noncomputable def tilingEquivClosedPath (w : ℕ) : Tiling m w ≃ StatePath (m := m) w ∅ :=
  (partialEmptyEquivTiling m w).symm.trans (partialTilingEquivPath w ∅)

theorem partial_path_roundtrip (w : ℕ) (S : State m) (P : PartialTiling m w S) :
    (partialTilingEquivPath w S).symm ((partialTilingEquivPath w S) P) = P :=
  (partialTilingEquivPath w S).symm_apply_apply P

theorem path_partial_roundtrip (w : ℕ) (S : State m) (P : StatePath w S) :
    (partialTilingEquivPath w S) ((partialTilingEquivPath w S).symm P) = P :=
  (partialTilingEquivPath w S).apply_symm_apply P

theorem partial_path_state {w : ℕ} {S : State m} (P : PartialTiling m w S) (k : ℕ) :
    ((partialTilingEquivPath w S) P).state k = gridH (gridOfPartial P) k := rfl

end Domino.General
