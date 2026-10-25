module

public import Domino.Board.Partial
public import Mathlib.Tactic

/-! 三行单列：输入、输出和两种可能的竖砖恰好覆盖各行一次。 -/

@[expose] public section

namespace Domino

def ColumnRule (p q : State 3) (v : Finset (Fin 2)) : Prop :=
  ∀ r : Fin 3,
    (if r ∈ p then 1 else 0) + (if r ∈ q then 1 else 0) +
    (if (r = 0 ∨ r = 1) ∧ 0 ∈ v then 1 else 0) +
    (if (r = 1 ∨ r = 2) ∧ 1 ∈ v then 1 else 0) = (1 : ℕ)

instance columnRuleDecidable (p q : State 3) (v : Finset (Fin 2)) :
    Decidable (ColumnRule p q v) := inferInstanceAs (Decidable (∀ _r : Fin 3, _))

def Legal3 (p q : State 3) : Prop :=
  Disjoint p q ∧
    ((Finset.univ \ (p ∪ q)) = ∅ ∨
     (Finset.univ \ (p ∪ q)) = {0, 1} ∨
     (Finset.univ \ (p ∪ q)) = {1, 2})

instance legal3Decidable (p q : State 3) : Decidable (Legal3 p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev ColumnCover (p q : State 3) := {v : Finset (Fin 2) // ColumnRule p q v}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem legal3_iff_column_cover : ∀ p q : State 3, Legal3 p q ↔ ∃ v, ColumnRule p q v := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem column_cover_unique : ∀ (p q : State 3) (v u : Finset (Fin 2)),
    ColumnRule p q v → ColumnRule p q u → v = u := by
  decide

instance columnCoverSubsingleton (p q : State 3) : Subsingleton (ColumnCover p q) :=
  ⟨fun a b => Subtype.ext (column_cover_unique p q a.val b.val a.property b.property)⟩

noncomputable def fillColumn (p q : State 3) (h : Legal3 p q) : ColumnCover p q :=
  ⟨((legal3_iff_column_cover p q).mp h).choose,
    ((legal3_iff_column_cover p q).mp h).choose_spec⟩

def transfer3 (p q : State 3) : ℕ := if Legal3 p q then 1 else 0

theorem columnCover_card (p q : State 3) : Fintype.card (ColumnCover p q) = transfer3 p q := by
  classical
  by_cases h : Legal3 p q
  · let _ : Unique (ColumnCover p q) :=
      { default := fillColumn p q h, uniq := fun _ => Subsingleton.elim _ _ }
    simp [transfer3, h]
  · have : IsEmpty (ColumnCover p q) := ⟨fun v => h ((legal3_iff_column_cover p q).mpr ⟨v.val, v.property⟩)⟩
    simp [transfer3, h]

end Domino
