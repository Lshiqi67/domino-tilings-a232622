module

public import Domino.OddHeight.Column

/-! 任意高度的列数据与几何邻居关系。 -/

@[expose] public section

namespace Domino.General

variable {m : ℕ}

def GridLink (H : ℕ → State m) (V : ℕ → RowBonds m) (a b : GridCell m) : Prop :=
  (a.1 = b.1 ∧ b.2 + 1 = a.2 ∧ a.1 ∈ H a.2) ∨
  (a.1 = b.1 ∧ b.2 = a.2 + 1 ∧ a.1 ∈ H (a.2 + 1)) ∨
  (b.2 = a.2 ∧ (a.1, b.1) ∈ V a.2)

@[simp] theorem gridLink_horizontal (H : ℕ → State m) (V : ℕ → RowBonds m) (r : Fin m) (i : ℕ) :
    GridLink H V (r, i) (r, i + 1) ↔ r ∈ H (i + 1) := by
  simp [GridLink, show i + 1 + 1 ≠ i by omega]

theorem gridLink_adjacent (H : ℕ → State m) (V : ℕ → RowBonds m)
    (hv : ∀ k r s, (r, s) ∈ V k → RowAdjacent r s)
    (a b : GridCell m) (h : GridLink H V a b) : GridAdjacent a b := by
  rcases h with ⟨hr, hc, _⟩ | ⟨hr, hc, _⟩ | ⟨hc, he⟩
  · exact Or.inl ⟨hr, Or.inr hc⟩
  · exact Or.inl ⟨hr, Or.inl hc.symm⟩
  · exact Or.inr ⟨hc.symm, hv _ _ _ he⟩

theorem gridLink_symmetric (H : ℕ → State m) (V : ℕ → RowBonds m)
    (hv : ∀ k r s, (r, s) ∈ V k → (s, r) ∈ V k)
    (a b : GridCell m) (h : GridLink H V a b) : GridLink H V b a := by
  rcases h with ⟨hr, hc, hm⟩ | ⟨hr, hc, hm⟩ | ⟨hc, he⟩
  · exact Or.inr (Or.inl ⟨hr.symm, hc.symm, by simpa [hr, hc] using hm⟩)
  · exact Or.inl ⟨hr.symm, hc.symm, by simpa [hr, hc] using hm⟩
  · exact Or.inr (Or.inr ⟨hc.symm, by simpa [hc] using hv _ _ _ he⟩)

@[simp] theorem gridLink_vertical (H : ℕ → State m) (V : ℕ → RowBonds m)
    (r s : Fin m) (i : ℕ) : GridLink H V (r, i) (s, i) ↔ (r, s) ∈ V i := by simp [GridLink]

theorem column_rule_neighbors (H : ℕ → State m) (V : ℕ → RowBonds m)
    (start : H 0 = ∅) (i : ℕ) (h : ColumnRule (H i) (H (i + 1)) (V i)) :
    ∀ r : Fin m, ∃! b, GridLink H V (r, i) b := by
  intro r
  have incoming_pos (hp : r ∈ H i) : 0 < i := by
    by_contra hz
    have hi : i = 0 := by omega
    simp [hi, start] at hp
  by_cases hp : r ∈ H i
  · have hip := incoming_pos hp
    refine ⟨(r, i - 1), Or.inl ⟨rfl, by dsimp; omega, hp⟩, ?_⟩
    rintro ⟨s, j⟩ (⟨hrs, hji, _⟩ | ⟨hrs, hji, hq⟩ | ⟨hji, hv⟩)
    · exact Prod.ext hrs.symm (by dsimp only at hji; omega)
    · exact (Finset.disjoint_left.mp h.1 hp hq).elim
    · have hn := (h.2.2.2.1 r).mp ⟨s, hv⟩
      exact (hn (Finset.mem_union_left _ hp)).elim
  · by_cases hq : r ∈ H (i + 1)
    · refine ⟨(r, i + 1), Or.inr (Or.inl ⟨rfl, rfl, hq⟩), ?_⟩
      rintro ⟨s, j⟩ (⟨_, _, hpp⟩ | ⟨hrs, hji, _⟩ | ⟨_, hv⟩)
      · exact (hp hpp).elim
      · exact Prod.ext hrs.symm hji
      · have hn := (h.2.2.2.1 r).mp ⟨s, hv⟩
        exact (hn (Finset.mem_union_right _ hq)).elim
    · have hn : r ∉ H i ∪ H (i + 1) := by simp [hp, hq]
      obtain ⟨s, hrs⟩ := (h.2.2.2.1 r).mpr hn
      refine ⟨(s, i), Or.inr (Or.inr ⟨rfl, hrs⟩), ?_⟩
      rintro ⟨t, j⟩ (⟨_, _, hpp⟩ | ⟨_, _, hqq⟩ | ⟨hji, hrt⟩)
      · exact (hp hpp).elim
      · exact (hq hqq).elim
      · exact Prod.ext (h.2.2.2.2 r t s hrt hrs) hji

theorem neighbors_column_rule (H : ℕ → State m) (V : ℕ → RowBonds m)
    (start : H 0 = ∅) (i : ℕ)
    (hadj : ∀ r s, (r, s) ∈ V i → RowAdjacent r s)
    (hsym : ∀ r s, (r, s) ∈ V i → (s, r) ∈ V i)
    (degree : ∀ r : Fin m, ∃! b, GridLink H V (r, i) b) :
    ColumnRule (H i) (H (i + 1)) (V i) := by
  have incoming_pos (r : Fin m) (hp : r ∈ H i) : 0 < i := by
    by_contra hz
    have hi : i = 0 := by omega
    simp [hi, start] at hp
  have unique (r : Fin m) (a b : GridCell m)
      (ha : GridLink H V (r, i) a) (hb : GridLink H V (r, i) b) : a = b := by
    obtain ⟨c, _, hc⟩ := degree r
    exact (hc a ha).trans (hc b hb).symm
  have left (r : Fin m) (hp : r ∈ H i) : GridLink H V (r, i) (r, i - 1) :=
    Or.inl ⟨rfl, by dsimp; have := incoming_pos r hp; omega, hp⟩
  have right (r : Fin m) (hq : r ∈ H (i + 1)) : GridLink H V (r, i) (r, i + 1) :=
    Or.inr (Or.inl ⟨rfl, rfl, hq⟩)
  have vert (r s : Fin m) (hv : (r, s) ∈ V i) : GridLink H V (r, i) (s, i) :=
    Or.inr (Or.inr ⟨rfl, hv⟩)
  refine ⟨Finset.disjoint_left.mpr ?_, hadj, hsym, ?_, ?_⟩
  · intro r hp hq
    have he := congrArg Prod.snd (unique r _ _ (left r hp) (right r hq))
    dsimp only at he
    omega
  · intro r
    constructor
    · rintro ⟨s, hv⟩ hm
      rcases Finset.mem_union.mp hm with hp | hq
      · have he := congrArg Prod.snd (unique r _ _ (left r hp) (vert r s hv))
        have hip := incoming_pos r hp
        dsimp only at he
        omega
      · have he := congrArg Prod.snd (unique r _ _ (right r hq) (vert r s hv))
        dsimp only at he
        omega
    · intro hn
      obtain ⟨⟨s, j⟩, hb, _⟩ := degree r
      rcases hb with ⟨_, _, hp⟩ | ⟨_, _, hq⟩ | ⟨_, hv⟩
      · exact (hn (Finset.mem_union_left _ hp)).elim
      · exact (hn (Finset.mem_union_right _ hq)).elim
      · exact ⟨s, hv⟩
  · intro r s t hs ht
    exact congrArg Prod.fst (unique r _ _ (vert r s hs) (vert r t ht))

end Domino.General
