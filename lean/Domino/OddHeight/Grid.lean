module

public import Domino.Transfer.Bonds

/-! 用自然数列坐标延拓有限棋盘配对，棋盘外关系为空；不改变计数对象。 -/

@[expose] public section

namespace Domino.General

variable {m : ℕ}

abbrev GridCell (m : ℕ) := Fin m × ℕ

def gridCell {w : ℕ} (c : Cell m w) : (GridCell m) := (c.1, c.2.val)

def GridAdjacent (a b : (GridCell m)) : Prop :=
  (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
  (a.2 = b.2 ∧ (a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val))

def GridLive (w : ℕ) (S : State m) (a : (GridCell m)) : Prop :=
  a.2 < w ∧ ¬(a.2 + 1 = w ∧ a.1 ∈ S)

structure GridMatching (w : ℕ) (S : State m) where
  rel : (GridCell m) → (GridCell m) → Prop
  guard : w = 0 → S = ∅
  adjacent : ∀ a b, rel a b → GridAdjacent a b
  symm : ∀ a b, rel a b → rel b a
  live : ∀ a, (∃ b, rel a b) ↔ GridLive w S a
  unique : ∀ a b c, rel a b → rel a c → b = c

@[ext] theorem gridMatching_ext {w : ℕ} {S : State m} (R Q : GridMatching w S)
    (h : ∀ a b, R.rel a b ↔ Q.rel a b) : R = Q := by
  have he : R.rel = Q.rel := funext fun a => funext fun b => propext (h a b)
  cases R
  cases Q
  cases he
  rfl

theorem grid_matching_bounds {w : ℕ} {S : State m} (R : GridMatching w S)
    {a b : (GridCell m)} (h : R.rel a b) : a.2 < w ∧ b.2 < w :=
  ⟨((R.live a).mp ⟨b, h⟩).1, ((R.live b).mp ⟨a, R.symm a b h⟩).1⟩

@[simp] theorem grid_adjacent_iff {w : ℕ} (a b : Cell m w) :
    GridAdjacent (gridCell a) (gridCell b) ↔ Adjacent a b := by
  simp [GridAdjacent, gridCell, Adjacent, Fin.ext_iff]

noncomputable def gridOfPartial {w : ℕ} {S : State m} (P : PartialTiling m w S) :
    GridMatching w S where
  rel a b := ∃ (ha : a.2 < w) (hb : b.2 < w),
    ((a.1, ⟨a.2, ha⟩), (b.1, ⟨b.2, hb⟩)) ∈ coverBonds P.val
  guard := P.property
  adjacent a b h := by
    obtain ⟨ha, hb, h⟩ := h
    exact (grid_adjacent_iff (a.1, ⟨a.2, ha⟩) (b.1, ⟨b.2, hb⟩)).mpr
      ((coverBonds_valid P.val).1 _ _ h)
  symm a b h := by
    obtain ⟨ha, hb, h⟩ := h
    exact ⟨hb, ha, (coverBonds_valid P.val).2.1 _ _ h⟩
  live a := by
    constructor
    · rintro ⟨b, ha, hb, hab⟩
      have hn := ((coverBonds_valid P.val).2.2.1 (a.1, ⟨a.2, ha⟩)).mp
        ⟨(b.1, ⟨b.2, hb⟩), hab⟩
      exact ⟨ha, by simpa using hn⟩
    · rintro ⟨ha, hn⟩
      have hnot : (a.1, ⟨a.2, ha⟩) ∉ terminalHoles m w S := by simpa using hn
      obtain ⟨b, hb⟩ := ((coverBonds_valid P.val).2.2.1 _).mpr hnot
      exact ⟨gridCell b, ha, b.2.isLt, hb⟩
  unique a b c hab hac := by
    obtain ⟨ha, hb, hab⟩ := hab
    obtain ⟨_, hc, hac⟩ := hac
    have he := (coverBonds_valid P.val).2.2.2 _ _ _ hab hac
    exact congrArg gridCell he

@[simp] theorem gridOfPartial_at {w : ℕ} {S : State m} (P : PartialTiling m w S)
    (a b : Cell m w) :
    (gridOfPartial P).rel (gridCell a) (gridCell b) ↔ (a, b) ∈ coverBonds P.val := by
  simp [gridOfPartial, gridCell]

noncomputable def finiteBonds {w : ℕ} {S : State m} (R : GridMatching w S) :
    BondCover m w (terminalHoles m w S) := by
  classical
  refine ⟨Finset.univ.filter (fun ab => R.rel (gridCell ab.1) (gridCell ab.2)), ?_⟩
  simp only [BondValid, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun a b h => (grid_adjacent_iff a b).mp (R.adjacent _ _ h),
    fun a b h => R.symm _ _ h, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨b, hb⟩
      have := ((R.live (gridCell a)).mp ⟨gridCell b, hb⟩).2
      simpa [gridCell] using this
    · intro ha
      have hl : GridLive w S (gridCell a) := ⟨a.2.isLt, by simpa [gridCell] using ha⟩
      obtain ⟨b, hb⟩ := (R.live _).mpr hl
      have hbw := (grid_matching_bounds R hb).2
      exact ⟨(b.1, ⟨b.2, hbw⟩), hb⟩
  · intro a b c hb hc
    have he := R.unique _ _ _ hb hc
    apply Prod.ext
    · exact congrArg (fun z : (GridCell m) => z.1) he
    · exact Fin.ext (congrArg (fun z : (GridCell m) => z.2) he)

@[simp] theorem mem_finiteBonds {w : ℕ} {S : State m} (R : GridMatching w S)
    (a b : Cell m w) : (a, b) ∈ (finiteBonds R).val ↔ R.rel (gridCell a) (gridCell b) := by
  classical
  simp [finiteBonds]

noncomputable def partialOfGrid {w : ℕ} {S : State m} (R : GridMatching w S) :
    PartialTiling m w S :=
  ⟨(coverEquivBonds m w (terminalHoles m w S)).symm (finiteBonds R), R.guard⟩

@[simp] theorem coverBonds_partialOfGrid {w : ℕ} {S : State m} (R : GridMatching w S) :
    coverBonds (partialOfGrid R).val = (finiteBonds R).val :=
  congrArg Subtype.val ((coverEquivBonds m w (terminalHoles m w S)).apply_symm_apply (finiteBonds R))

noncomputable def partialEquivGrid (w : ℕ) (S : State m) :
    PartialTiling m w S ≃ GridMatching w S where
  toFun := gridOfPartial
  invFun := partialOfGrid
  left_inv P := by
    apply Subtype.ext
    apply (coverEquivBonds m w (terminalHoles m w S)).injective
    apply Subtype.ext
    change coverBonds (partialOfGrid (gridOfPartial P)).val = coverBonds P.val
    rw [coverBonds_partialOfGrid]
    ext ab
    rcases ab with ⟨a, b⟩
    simp
  right_inv R := by
    apply gridMatching_ext
    intro a b
    change (∃ (ha : a.2 < w) (hb : b.2 < w),
      ((a.1, ⟨a.2, ha⟩), (b.1, ⟨b.2, hb⟩)) ∈ coverBonds (partialOfGrid R).val) ↔ R.rel a b
    rw [coverBonds_partialOfGrid]
    constructor
    · rintro ⟨ha, hb, h⟩
      exact (mem_finiteBonds R _ _).mp h
    · intro h
      have hh := grid_matching_bounds R h
      exact ⟨hh.1, hh.2, (mem_finiteBonds R _ _).mpr h⟩

end Domino.General
