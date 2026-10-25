module

public import Domino.Board.Tiling

/-! 半棋盘对象只含内部完整砖；末列留空格由终端行集合指定。 -/

@[expose] public section

namespace Domino

abbrev State (m : ℕ) := Finset (Fin m)

def reverseState {m : ℕ} (S : State m) : State m := S.map Fin.revPerm.toEmbedding

@[simp] theorem mem_reverseState {m : ℕ} (S : State m) (r : Fin m) :
    r ∈ reverseState S ↔ r.rev ∈ S := Finset.mem_map_equiv

@[simp] theorem reverseState_twice {m : ℕ} (S : State m) :
    reverseState (reverseState S) = S := by
  ext r
  simp only [mem_reverseState, Fin.rev_rev]

@[simp] theorem reverseState_empty (m : ℕ) : reverseState (∅ : State m) = ∅ := rfl

def terminalHoles (m w : ℕ) (S : State m) : Finset (Cell m w) :=
  Finset.univ.filter fun c => c.2.val + 1 = w ∧ c.1 ∈ S

@[simp] theorem mem_terminalHoles {m w : ℕ} (S : State m) (c : Cell m w) :
    c ∈ terminalHoles m w S ↔ c.2.val + 1 = w ∧ c.1 ∈ S := by
  simp [terminalHoles]

@[simp] theorem terminalHoles_empty (m w : ℕ) : terminalHoles m w ∅ = ∅ := by
  ext c
  simp

@[simp] theorem terminalHoles_width_zero (m : ℕ) (S : State m) :
    terminalHoles m 0 S = ∅ := by
  ext c
  exact Fin.elim0 c.2

/-- 宽零守卫排除无末列却携带非空终端的伪对象。 -/
abbrev PartialTiling (m w : ℕ) (S : State m) :=
  {_T : Cover m w (terminalHoles m w S) // w = 0 → S = ∅}

noncomputable instance partialTilingFintype (m w : ℕ) (S : State m) : Fintype (PartialTiling m w S) := by
  classical
  exact inferInstanceAs (Fintype {_T : Cover m w (terminalHoles m w S) // w = 0 → S = ∅})

noncomputable instance partialTilingDecidableEq (m w : ℕ) (S : State m) : DecidableEq (PartialTiling m w S) :=
  Classical.decEq _

def partialEmptyEquivTiling (m w : ℕ) : PartialTiling m w ∅ ≃ Tiling m w where
  toFun P := ⟨P.val.val, by simpa using P.val.property⟩
  invFun T := ⟨⟨T.val, by simpa using T.property⟩, fun _ => rfl⟩
  left_inv P := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv T := by apply Subtype.ext; rfl

theorem partial_width_zero_state {m : ℕ} {S : State m} (P : PartialTiling m 0 S) :
    S = ∅ := P.property rfl

theorem partial_width_zero_nonempty_iff (m : ℕ) (S : State m) :
    Nonempty (PartialTiling m 0 S) ↔ S = ∅ := by
  constructor
  · rintro ⟨P⟩
    exact partial_width_zero_state P
  · rintro rfl
    exact ⟨(partialEmptyEquivTiling m 0).symm (emptyWidthTiling m)⟩

theorem partial_width_zero_isEmpty {m : ℕ} {S : State m} (hS : S ≠ ∅) :
    IsEmpty (PartialTiling m 0 S) := ⟨fun P => hS (partial_width_zero_state P)⟩

instance partialWidthZeroUnique (m : ℕ) : Unique (PartialTiling m 0 ∅) where
  default := (partialEmptyEquivTiling m 0).symm (emptyWidthTiling m)
  uniq P := (partialEmptyEquivTiling m 0).injective
    (Subsingleton.elim ((partialEmptyEquivTiling m 0) P) _)

theorem partial_width_zero_card (m : ℕ) (S : State m) :
    Fintype.card (PartialTiling m 0 S) = if S = ∅ then 1 else 0 := by
  classical
  by_cases hS : S = ∅
  · subst S
    simp
  · let _ := partial_width_zero_isEmpty hS
    simp [hS]

theorem partial_empty_card (m w : ℕ) :
    Fintype.card (PartialTiling m w ∅) = Fintype.card (Tiling m w) :=
  Fintype.card_congr (partialEmptyEquivTiling m w)

end Domino
