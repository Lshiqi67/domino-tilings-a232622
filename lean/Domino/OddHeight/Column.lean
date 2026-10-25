module

public import Domino.OddHeight.Grid
public import Mathlib.Tactic

/-! 任意高度的竖直配对。归纳唯一性使用每行至多两个相邻行，不使用固定高度穷举。 -/

@[expose] public section

namespace Domino.General

variable {m : ℕ}

abbrev RowBonds (m : ℕ) := Finset (Fin m × Fin m)

def RowAdjacent (r s : Fin m) : Prop := r.val + 1 = s.val ∨ s.val + 1 = r.val

def RowValid (H : State m) (V : RowBonds m) : Prop :=
  (∀ r s, (r, s) ∈ V → RowAdjacent r s) ∧
  (∀ r s, (r, s) ∈ V → (s, r) ∈ V) ∧
  (∀ r, (∃ s, (r, s) ∈ V) ↔ r ∉ H) ∧
  (∀ r s t, (r, s) ∈ V → (r, t) ∈ V → s = t)

abbrev RowCover (H : State m) := {V : RowBonds m // RowValid H V}

noncomputable instance rowCoverFintype (H : State m) : Fintype (RowCover H) := Fintype.ofFinite _

theorem row_cover_unique (H : State m) (V W : RowCover H) : V = W := by
  have h : ∀ i : ℕ, ∀ r : Fin m, r.val = i → ∀ s, (r, s) ∈ V.val ↔ (r, s) ∈ W.val := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro r hr s
      have forward (A B : RowCover H)
          (prev : ∀ t : Fin m, t.val < i → ∀ u, (t, u) ∈ A.val ↔ (t, u) ∈ B.val)
          (hrs : (r, s) ∈ A.val) : (r, s) ∈ B.val := by
        rcases A.property.1 r s hrs with hd | hu
        · have live : r ∉ H := (A.property.2.2.1 r).mp ⟨s, hrs⟩
          obtain ⟨t, hrt⟩ := (B.property.2.2.1 r).mpr live
          rcases B.property.1 r t hrt with htd | htu
          · have he : t = s := Fin.ext (by omega)
            simpa [he] using hrt
          · have ht : t.val < i := by omega
            have htr := (prev t ht r).mpr (B.property.2.1 r t hrt)
            have he := A.property.2.2.2 r s t hrs (A.property.2.1 t r htr)
            have := congrArg Fin.val he
            omega
        · have hs : s.val < i := by omega
          exact B.property.2.1 s r ((prev s hs r).mp (A.property.2.1 r s hrs))
      constructor
      · exact forward V W (fun t ht u => ih t.val ht t rfl u)
      · exact forward W V (fun t ht u => (ih t.val ht t rfl u).symm)
  apply Subtype.ext
  ext rs
  exact h rs.1.val rs.1 rfl rs.2

instance rowCoverSubsingleton (H : State m) : Subsingleton (RowCover H) := ⟨row_cover_unique H⟩

def ColumnRule (p q : State m) (V : RowBonds m) : Prop := Disjoint p q ∧ RowValid (p ∪ q) V

def Legal (p q : State m) : Prop := Disjoint p q ∧ Nonempty (RowCover (p ∪ q))

noncomputable instance legalDecidable (p q : State m) : Decidable (Legal p q) := Classical.propDecidable _

abbrev ColumnCover (p q : State m) := {V : RowBonds m // ColumnRule p q V}

theorem legal_iff_column_cover (p q : State m) : Legal p q ↔ ∃ V, ColumnRule p q V := by
  constructor
  · rintro ⟨hd, ⟨⟨V, hV⟩⟩⟩; exact ⟨V, hd, hV⟩
  · rintro ⟨V, hd, hV⟩; exact ⟨hd, ⟨⟨V, hV⟩⟩⟩

theorem column_cover_unique (p q : State m) (V W : RowBonds m)
    (hV : ColumnRule p q V) (hW : ColumnRule p q W) : V = W :=
  congrArg Subtype.val (row_cover_unique (p ∪ q) ⟨V, hV.2⟩ ⟨W, hW.2⟩)

noncomputable def fillColumn (p q : State m) (h : Legal p q) : ColumnCover p q :=
  ⟨((legal_iff_column_cover p q).mp h).choose, ((legal_iff_column_cover p q).mp h).choose_spec⟩

theorem legal_symm (p q : State m) : Legal p q ↔ Legal q p := by
  simp only [Legal, Finset.union_comm p q, disjoint_comm]

theorem legal_self_iff (p : State m) : Legal p p ↔ p = ∅ ∧ Legal (∅ : State m) ∅ := by
  constructor
  · intro h
    have hp : p = ∅ := by simpa using h.1
    exact ⟨hp, by simpa [hp] using h⟩
  · rintro ⟨rfl, h⟩; exact h

noncomputable def transfer (p q : State m) : ℕ := if Legal p q then 1 else 0

end Domino.General
