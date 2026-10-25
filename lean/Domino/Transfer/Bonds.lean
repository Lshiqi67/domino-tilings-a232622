module

public import Domino.Board.Partial
public import Mathlib.Tactic

/-! 无序砖覆盖与有向相邻配对关系的等价。辅助关系仍由实际格子组成。 -/

@[expose] public section

namespace Domino

abbrev Bonds (m w : ℕ) := Finset (Cell m w × Cell m w)

def BondValid {m w : ℕ} (H : Finset (Cell m w)) (R : Bonds m w) : Prop :=
  (∀ a b, (a, b) ∈ R → Adjacent a b) ∧
  (∀ a b, (a, b) ∈ R → (b, a) ∈ R) ∧
  (∀ a, (∃ b, (a, b) ∈ R) ↔ a ∉ H) ∧
  (∀ a b c, (a, b) ∈ R → (a, c) ∈ R → b = c)

abbrev BondCover (m w : ℕ) (H : Finset (Cell m w)) :=
  {R : Bonds m w // BondValid H R}

theorem edge_pair_at {m w : ℕ} (e : Edge m w) {a : Cell m w} (ha : a ∈ e.val) :
    ∃ b, Adjacent a b ∧ e.val = {a, b} := by
  obtain ⟨x, y, hxy, he⟩ := e.property
  simp only [he, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨y, hxy, he⟩
  · exact ⟨x, adjacent_symm hxy, he.trans (Finset.pair_comm _ _)⟩

theorem pair_partner_unique {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (_hac : a ≠ c) (h : ({a, b} : Finset α) = {a, c}) : b = c := by
  have hb : b ∈ ({a, c} : Finset α) := h ▸ (by simp)
  simpa [Ne.symm hab] using hb

noncomputable def coverBonds {m w : ℕ} {H : Finset (Cell m w)}
    (T : Cover m w H) : Bonds m w := by
  classical
  exact Finset.univ.filter fun ab => ∃ e ∈ T.val, e.val = {ab.1, ab.2}

@[simp] theorem mem_coverBonds {m w : ℕ} {H : Finset (Cell m w)}
    (T : Cover m w H) (a b : Cell m w) :
    (a, b) ∈ coverBonds T ↔ ∃ e ∈ T.val, e.val = {a, b} := by
  classical
  simp [coverBonds]

theorem coverBonds_valid {m w : ℕ} {H : Finset (Cell m w)} (T : Cover m w H) :
    BondValid H (coverBonds T) := by
  classical
  have adj (a b : Cell m w) (h : (a, b) ∈ coverBonds T) : Adjacent a b := by
    obtain ⟨e, _, he⟩ := (mem_coverBonds T a b).mp h
    obtain ⟨x, y, hxy, hE⟩ := e.property
    have hab : a ≠ b := by
      intro hh
      have := edge_card_two e
      simp [he, hh] at this
    have ha : a = x ∨ a = y := by
      have : a ∈ e.val := by simp [he]
      simpa [hE] using this
    have hb : b = x ∨ b = y := by
      have : b ∈ e.val := by simp [he]
      simpa [hE] using this
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hxy
    · exact adjacent_symm hxy
    · exact (hab rfl).elim
  refine ⟨adj, ?_, ?_, ?_⟩
  · intro a b h
    obtain ⟨e, he, hab⟩ := (mem_coverBonds T a b).mp h
    exact (mem_coverBonds T b a).mpr ⟨e, he, hab.trans (Finset.pair_comm a b)⟩
  · intro a
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨e, he, hab⟩ := (mem_coverBonds T a b).mp hb
      exact (T.property.1 a).mp ⟨e, he, by simp [hab]⟩
    · intro ha
      obtain ⟨e, he, hae⟩ := (T.property.1 a).mpr ha
      obtain ⟨b, _, hab⟩ := edge_pair_at e hae
      exact ⟨b, (mem_coverBonds T a b).mpr ⟨e, he, hab⟩⟩
  · intro a b c hb hc
    obtain ⟨e, he, hab⟩ := (mem_coverBonds T a b).mp hb
    obtain ⟨f, hf, hac⟩ := (mem_coverBonds T a c).mp hc
    have hef : e = f := T.property.2 e he f hf a (by simp [hab]) (by simp [hac])
    exact pair_partner_unique (adjacent_ne (adj a b hb)) (adjacent_ne (adj a c hc))
      (hab.symm.trans ((congrArg Subtype.val hef).trans hac))

noncomputable def bondEdges {m w : ℕ} {H : Finset (Cell m w)}
    (R : BondCover m w H) : Finset (Edge m w) := by
  classical
  exact Finset.univ.filter fun e => ∃ a b, (a, b) ∈ R.val ∧ e.val = {a, b}

@[simp] theorem mem_bondEdges {m w : ℕ} {H : Finset (Cell m w)}
    (R : BondCover m w H) (e : Edge m w) :
    e ∈ bondEdges R ↔ ∃ a b, (a, b) ∈ R.val ∧ e.val = {a, b} := by
  classical
  simp [bondEdges]

theorem bondEdges_at {m w : ℕ} {H : Finset (Cell m w)} (R : BondCover m w H)
    (e : Edge m w) (he : e ∈ bondEdges R) {a : Cell m w} (ha : a ∈ e.val) :
    ∃ b, (a, b) ∈ R.val ∧ e.val = {a, b} := by
  obtain ⟨x, y, hxy, heq⟩ := (mem_bondEdges R e).mp he
  simp only [heq, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨y, hxy, heq⟩
  · exact ⟨x, R.property.2.1 _ _ hxy, heq.trans (Finset.pair_comm _ _)⟩

theorem bondEdges_valid {m w : ℕ} {H : Finset (Cell m w)} (R : BondCover m w H) :
    IsCover H (bondEdges R) := by
  constructor
  · intro a
    constructor
    · rintro ⟨e, he, ha⟩
      obtain ⟨b, hb, _⟩ := bondEdges_at R e he ha
      exact (R.property.2.2.1 a).mp ⟨b, hb⟩
    · intro ha
      obtain ⟨b, hb⟩ := (R.property.2.2.1 a).mpr ha
      let e := edgeOfAdjacent a b (R.property.1 a b hb)
      exact ⟨e, (mem_bondEdges R e).mpr ⟨a, b, hb, rfl⟩, by simp [e, edgeOfAdjacent]⟩
  · intro e he f hf a hae haf
    obtain ⟨b, hb, heq⟩ := bondEdges_at R e he hae
    obtain ⟨c, hc, hfq⟩ := bondEdges_at R f hf haf
    have hbc := R.property.2.2.2 a b c hb hc
    apply Subtype.ext
    simp [heq, hfq, hbc]

noncomputable def coverEquivBonds (m w : ℕ) (H : Finset (Cell m w)) :
    Cover m w H ≃ BondCover m w H where
  toFun T := ⟨coverBonds T, coverBonds_valid T⟩
  invFun R := ⟨bondEdges R, bondEdges_valid R⟩
  left_inv T := by
    apply Subtype.ext
    ext e
    simp only [mem_bondEdges, mem_coverBonds]
    constructor
    · rintro ⟨a, b, ⟨f, hf, hfq⟩, heq⟩
      have : e = f := Subtype.ext (heq.trans hfq.symm)
      simpa [this] using hf
    · intro he
      obtain ⟨a, b, _, heq⟩ := e.property
      exact ⟨a, b, ⟨e, he, heq⟩, heq⟩
  right_inv R := by
    apply Subtype.ext
    ext ab
    obtain ⟨a, b⟩ := ab
    simp only [mem_coverBonds]
    constructor
    · rintro ⟨e, he, heq⟩
      obtain ⟨c, hc, hcq⟩ := bondEdges_at R e he (a := a) (by simp [heq])
      have hcb : c = b := pair_partner_unique (adjacent_ne (R.property.1 a c hc))
        (by intro hab; have := edge_card_two e; simp [heq, hab] at this)
        (hcq.symm.trans heq)
      simpa [hcb] using hc
    · intro hab
      let e := edgeOfAdjacent a b (R.property.1 a b hab)
      exact ⟨e, (mem_bondEdges R e).mpr ⟨a, b, hab, rfl⟩, rfl⟩

end Domino
