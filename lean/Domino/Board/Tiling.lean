module

public import Domino.Board.Basic

/-! 无序多米诺与精确覆盖。所有计数对象均是有限集合的子类型。 -/

@[expose] public section

namespace Domino

def IsEdge {m w : ℕ} (s : Finset (Cell m w)) : Prop :=
  ∃ a b, Adjacent a b ∧ s = {a, b}

abbrev Edge (m w : ℕ) := {s : Finset (Cell m w) // IsEdge s}

noncomputable instance edgeFintype {m w : ℕ} : Fintype (Edge m w) := by
  classical
  exact inferInstanceAs (Fintype {s : Finset (Cell m w) // IsEdge s})

def edgeOfAdjacent {m w : ℕ} (a b : Cell m w) (h : Adjacent a b) : Edge m w :=
  ⟨{a, b}, a, b, h, rfl⟩

theorem edgeOfAdjacent_swap {m w : ℕ} (a b : Cell m w) (h : Adjacent a b) :
    edgeOfAdjacent a b h = edgeOfAdjacent b a (adjacent_symm h) := by
  apply Subtype.ext
  exact Finset.pair_comm a b

theorem edge_card_two {m w : ℕ} (e : Edge m w) : e.val.card = 2 := by
  rcases e.property with ⟨a, b, h, he⟩
  rw [he]
  simp [adjacent_ne h]

theorem edge_nonempty {m w : ℕ} (e : Edge m w) : e.val.Nonempty := by
  rcases e.property with ⟨a, b, _, he⟩
  exact ⟨a, by simp [he]⟩

instance edgeWidthZeroIsEmpty {m : ℕ} : IsEmpty (Edge m 0) := ⟨fun e => by
  obtain ⟨c, _⟩ := edge_nonempty e
  exact Fin.elim0 c.2⟩

instance edgeHeightZeroIsEmpty {w : ℕ} : IsEmpty (Edge 0 w) := ⟨fun e => by
  obtain ⟨c, _⟩ := edge_nonempty e
  exact Fin.elim0 c.1⟩

/-- 覆盖的格恰为洞集的补集；任何共享格子的两块砖必须相等。 -/
def IsCover {m w : ℕ} (holes : Finset (Cell m w)) (edges : Finset (Edge m w)) : Prop :=
  (∀ c, (∃ e ∈ edges, c ∈ e.val) ↔ c ∉ holes) ∧
  (∀ e ∈ edges, ∀ f ∈ edges, ∀ c, c ∈ e.val → c ∈ f.val → e = f)

abbrev Cover (m w : ℕ) (holes : Finset (Cell m w)) :=
  {edges : Finset (Edge m w) // IsCover holes edges}

abbrev Tiling (m w : ℕ) := Cover m w ∅

noncomputable instance coverFintype {m w : ℕ} {holes : Finset (Cell m w)} :
    Fintype (Cover m w holes) := Fintype.ofFinite _

theorem tiling_finite (m w : ℕ) : Finite (Tiling m w) := inferInstance

theorem cover_exactly_one {m w : ℕ} {holes : Finset (Cell m w)}
    (T : Cover m w holes) (c : Cell m w) (hc : c ∉ holes) :
    ∃! e, e ∈ T.val ∧ c ∈ e.val := by
  obtain ⟨e, he, hce⟩ := (T.property.1 c).mpr hc
  refine ⟨e, ⟨he, hce⟩, ?_⟩
  intro f hf
  exact T.property.2 f hf.1 e he c hf.2 hce

theorem cover_avoids_holes {m w : ℕ} {holes : Finset (Cell m w)}
    (T : Cover m w holes) {c : Cell m w} (hc : c ∈ holes)
    {e : Edge m w} (he : e ∈ T.val) : c ∉ e.val := by
  intro hce
  exact (T.property.1 c).mp ⟨e, he, hce⟩ hc

theorem isCover_empty_iff {m w : ℕ} (edges : Finset (Edge m w)) :
    IsCover ∅ edges ↔ ∀ c, ∃! e, e ∈ edges ∧ c ∈ e.val := by
  constructor
  · intro h c
    exact cover_exactly_one ⟨edges, h⟩ c (Finset.notMem_empty c)
  · intro h
    constructor
    · intro c
      constructor
      · intro _
        exact Finset.notMem_empty c
      · intro _
        obtain ⟨e, he, _⟩ := h c
        exact ⟨e, he⟩
    · intro e he f hf c hce hcf
      obtain ⟨g, _, hg⟩ := h c
      exact (hg e ⟨he, hce⟩).trans (hg f ⟨hf, hcf⟩).symm

def emptyWidthTiling (m : ℕ) : Tiling m 0 := ⟨∅, by
  constructor
  · intro c
    exact Fin.elim0 c.2
  · intro e
    exact isEmptyElim e⟩

def emptyHeightTiling (w : ℕ) : Tiling 0 w := ⟨∅, by
  constructor
  · intro c
    exact Fin.elim0 c.1
  · intro e
    exact isEmptyElim e⟩

instance tilingWidthZeroUnique (m : ℕ) : Unique (Tiling m 0) where
  default := emptyWidthTiling m
  uniq T := by
    apply Subtype.ext
    ext e
    exact isEmptyElim e

instance tilingHeightZeroUnique (w : ℕ) : Unique (Tiling 0 w) where
  default := emptyHeightTiling w
  uniq T := by
    apply Subtype.ext
    ext e
    exact isEmptyElim e

theorem empty_tiling_unique (m : ℕ) (T : Tiling m 0) : T = emptyWidthTiling m :=
  Subsingleton.elim _ _

@[simp] theorem tiling_card_width_zero (m : ℕ) : Fintype.card (Tiling m 0) = 1 :=
  Fintype.card_unique

@[simp] theorem tiling_card_height_zero (w : ℕ) : Fintype.card (Tiling 0 w) = 1 :=
  Fintype.card_unique

end Domino
