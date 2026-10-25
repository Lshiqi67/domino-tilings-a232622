module

public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype

/-! 有限矩形的零基坐标与共边邻接。允许高度或宽度为零。 -/

@[expose] public section

namespace Domino

abbrev Cell (m w : ℕ) := Fin m × Fin w

def Adjacent {m w : ℕ} (a b : Cell m w) : Prop :=
  (a.1 = b.1 ∧ (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)) ∨
  (a.2 = b.2 ∧ (a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val))

instance adjacentDecidable {m w : ℕ} : DecidableRel (@Adjacent m w) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

theorem adjacent_symm {m w : ℕ} {a b : Cell m w} (h : Adjacent a b) :
    Adjacent b a := by
  rcases h with ⟨h, h'⟩ | ⟨h, h'⟩
  · exact Or.inl ⟨h.symm, h'.symm⟩
  · exact Or.inr ⟨h.symm, h'.symm⟩

theorem adjacent_ne {m w : ℕ} {a b : Cell m w} (h : Adjacent a b) : a ≠ b := by
  rintro rfl
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

def reflectRows {m w : ℕ} (c : Cell m w) : Cell m w := (c.1.rev, c.2)
def reflectCols {m w : ℕ} (c : Cell m w) : Cell m w := (c.1, c.2.rev)

@[simp] theorem reflectRows_twice {m w : ℕ} (c : Cell m w) :
    reflectRows (reflectRows c) = c := by simp [reflectRows]

@[simp] theorem reflectCols_twice {m w : ℕ} (c : Cell m w) :
    reflectCols (reflectCols c) = c := by simp [reflectCols]

theorem reflections_commute {m w : ℕ} (c : Cell m w) :
    reflectRows (reflectCols c) = reflectCols (reflectRows c) := rfl

theorem fin_rev_neighbor_iff {k : ℕ} (a b : Fin k) :
    (a.rev.val + 1 = b.rev.val ∨ b.rev.val + 1 = a.rev.val) ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by
  simp only [Fin.val_rev]
  have ha := a.isLt
  have hb := b.isLt
  omega

@[simp] theorem adjacent_reflectRows_iff {m w : ℕ} (a b : Cell m w) :
    Adjacent (reflectRows a) (reflectRows b) ↔ Adjacent a b := by
  simp only [Adjacent, reflectRows, Fin.rev_inj, fin_rev_neighbor_iff]

@[simp] theorem adjacent_reflectCols_iff {m w : ℕ} (a b : Cell m w) :
    Adjacent (reflectCols a) (reflectCols b) ↔ Adjacent a b := by
  simp only [Adjacent, reflectCols, Fin.rev_inj, fin_rev_neighbor_iff]

end Domino
