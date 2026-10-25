module

public import Domino.Transfer.Links

/-! 任意宽度的列分解：切口集合及列内竖砖与实际配对关系互逆。 -/

@[expose] public section

namespace Domino

structure ColumnFrame (w : ℕ) (S : State 3) where
  horizontal : ℕ → State 3
  vertical : ℕ → Finset (Fin 2)
  start : horizontal 0 = ∅
  finish : horizontal w = S
  hsupport : ∀ k, w < k → horizontal k = ∅
  vsupport : ∀ k, w ≤ k → vertical k = ∅
  column : ∀ k, k < w → ColumnRule (horizontal k) (horizontal (k + 1)) (vertical k)

@[ext] theorem columnFrame_ext {w : ℕ} {S : State 3} (F G : ColumnFrame w S)
    (hh : F.horizontal = G.horizontal) (hv : F.vertical = G.vertical) : F = G := by
  cases F
  cases G
  cases hh
  cases hv
  rfl

theorem frame_hbound {w : ℕ} {S : State 3} (F : ColumnFrame w S) {k : ℕ} {r : Fin 3}
    (h : r ∈ F.horizontal k) : k ≤ w := by
  by_contra hk
  have := F.hsupport k (by omega)
  simp [this] at h

def gridOfFrame {w : ℕ} {S : State 3} (F : ColumnFrame w S) : GridMatching w S where
  rel a b := a.2 < w ∧ b.2 < w ∧ GridLink F.horizontal F.vertical a b
  guard h := by simpa [h, F.start] using F.finish.symm
  adjacent a b h := gridLink_adjacent _ _ a b h.2.2
  symm a b h := ⟨h.2.1, h.1, gridLink_symmetric _ _ a b h.2.2⟩
  live a := by
    have degree (ha : a.2 < w) :=
      (columnRule_iff_unique_neighbors _ _ F.start a.2).mp (F.column a.2 ha) a.1
    constructor
    · rintro ⟨b, ha, hb, hab⟩
      refine ⟨ha, ?_⟩
      rintro ⟨hlast, hS⟩
      have hstub : GridLink F.horizontal F.vertical a (a.1, w) :=
        Or.inr (Or.inl ⟨rfl, hlast.symm, by simpa [hlast, F.finish] using hS⟩)
      obtain ⟨c, _, hu⟩ := degree ha
      have he := (hu b hab).trans (hu (a.1, w) hstub).symm
      have := congrArg Prod.snd he
      omega
    · rintro ⟨ha, hn⟩
      obtain ⟨b, hb, _⟩ := degree ha
      refine ⟨b, ha, ?_, hb⟩
      rcases hb with ⟨_, hc, _⟩ | ⟨_, hc, hm⟩ | ⟨hc, _, _⟩ | ⟨hc, _, _⟩
      · omega
      · have hle := frame_hbound F hm
        by_contra hbw
        have he : a.2 + 1 = w := by omega
        exact hn ⟨he, by simpa [he, F.finish] using hm⟩
      · omega
      · omega
  unique a b c hb hc := by
    obtain ⟨d, _, hu⟩ :=
      (columnRule_iff_unique_neighbors _ _ F.start a.2).mp (F.column a.2 hb.1) a.1
    exact (hu b hb.2.2).trans (hu c hc.2.2).symm

noncomputable def gridH {w : ℕ} {S : State 3} (R : GridMatching w S) (k : ℕ) : State 3 := by
  classical
  exact Finset.univ.filter fun r => (k = w ∧ r ∈ S) ∨ ∃ j, j + 1 = k ∧ R.rel (r, j) (r, k)

noncomputable def gridV {w : ℕ} {S : State 3} (R : GridMatching w S) (k : ℕ) : Finset (Fin 2) := by
  classical
  exact Finset.univ.filter fun r => R.rel (r.castSucc, k) (r.succ, k)

@[simp] theorem mem_gridH {w : ℕ} {S : State 3} (R : GridMatching w S) (k : ℕ) (r : Fin 3) :
    r ∈ gridH R k ↔ (k = w ∧ r ∈ S) ∨ ∃ j, j + 1 = k ∧ R.rel (r, j) (r, k) := by
  classical
  simp [gridH]

@[simp] theorem mem_gridV {w : ℕ} {S : State 3} (R : GridMatching w S) (k : ℕ) (r : Fin 2) :
    r ∈ gridV R k ↔ R.rel (r.castSucc, k) (r.succ, k) := by
  classical
  simp [gridV]

theorem gridH_start {w : ℕ} {S : State 3} (R : GridMatching w S) : gridH R 0 = ∅ := by
  ext r
  simp only [mem_gridH, Finset.notMem_empty, iff_false]
  rintro (⟨hw, hr⟩ | ⟨j, hj, _⟩)
  · have := R.guard hw.symm
    simp [this] at hr
  · omega

theorem gridH_finish {w : ℕ} {S : State 3} (R : GridMatching w S) : gridH R w = S := by
  ext r
  simp only [mem_gridH, true_and]
  constructor
  · rintro (h | ⟨j, _, h⟩)
    · exact h
    · have := (grid_matching_bounds R h).2
      omega
  · exact Or.inl

theorem gridH_support {w : ℕ} {S : State 3} (R : GridMatching w S)
    (k : ℕ) (hk : w < k) : gridH R k = ∅ := by
  ext r
  simp only [mem_gridH, Finset.notMem_empty, iff_false]
  rintro (⟨hw, _⟩ | ⟨j, _, h⟩)
  · omega
  · have := (grid_matching_bounds R h).2
    omega

theorem gridV_support {w : ℕ} {S : State 3} (R : GridMatching w S)
    (k : ℕ) (hk : w ≤ k) : gridV R k = ∅ := by
  ext r
  simp only [mem_gridV, Finset.notMem_empty, iff_false]
  intro h
  have := (grid_matching_bounds R h).1
  omega

def GridCompletion {w : ℕ} {S : State 3} (R : GridMatching w S) (a b : GridCell) : Prop :=
  R.rel a b ∨ (a.1 = b.1 ∧ a.1 ∈ S ∧
    ((a.2 + 1 = w ∧ b.2 = w) ∨ (b.2 + 1 = w ∧ a.2 = w)))

theorem three_row_neighbors : ∀ r s : Fin 3,
    (r.val + 1 = s.val ∨ s.val + 1 = r.val) ↔
    (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 0) ∨ (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1) := by
  decide

theorem gridLink_extract_iff {w : ℕ} {S : State 3} (R : GridMatching w S)
    (a b : GridCell) : GridLink (gridH R) (gridV R) a b ↔ GridCompletion R a b := by
  rcases a with ⟨r, i⟩
  rcases b with ⟨s, j⟩
  constructor
  · intro h
    rcases h with ⟨hr, hc, hm⟩ | ⟨hr, hc, hm⟩ | ⟨hc, hr, hm⟩ | ⟨hc, hr, hm⟩
    · dsimp only at hr hc hm
      subst s
      rcases (mem_gridH R i r).mp hm with ⟨hi, hs⟩ | ⟨k, hk, hR⟩
      · exact Or.inr ⟨rfl, hs, Or.inr ⟨hc.trans hi, hi⟩⟩
      · have : k = j := by omega
        subst k
        exact Or.inl (R.symm _ _ hR)
    · dsimp only at hr hc hm
      subst s
      subst j
      rcases (mem_gridH R (i + 1) r).mp hm with ⟨hi, hs⟩ | ⟨k, hk, hR⟩
      · exact Or.inr ⟨rfl, hs, Or.inl ⟨hi, hi⟩⟩
      · have : k = i := by omega
        subst k
        exact Or.inl hR
    · dsimp only at hc hr hm
      subst j
      have hR := (mem_gridV R i 0).mp hm
      rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hR
      · exact Or.inl (R.symm _ _ hR)
    · dsimp only at hc hr hm
      subst j
      have hR := (mem_gridV R i 1).mp hm
      rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hR
      · exact Or.inl (R.symm _ _ hR)
  · rintro (hR | ⟨hr, hs, hc⟩)
    · rcases R.adjacent _ _ hR with ⟨hr, hc | hc⟩ | ⟨hc, hr⟩
      · dsimp only at hr hc
        subst s
        exact Or.inr (Or.inl ⟨rfl, hc.symm,
          (mem_gridH R (i + 1) r).mpr (Or.inr ⟨i, rfl, by simpa [hc] using hR⟩)⟩)
      · dsimp only at hr hc
        subst s
        exact Or.inl ⟨rfl, hc,
          (mem_gridH R i r).mpr (Or.inr ⟨j, hc, R.symm _ _ hR⟩)⟩
      · dsimp only at hc hr
        subst j
        rcases (three_row_neighbors r s).mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩, (mem_gridV R i 0).mpr hR⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩, (mem_gridV R i 0).mpr (R.symm _ _ hR)⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩, (mem_gridV R i 1).mpr hR⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩, (mem_gridV R i 1).mpr (R.symm _ _ hR)⟩))
    · dsimp only at hr hs hc
      subst s
      rcases hc with ⟨hi, hj⟩ | ⟨hj, hi⟩
      · exact Or.inr (Or.inl ⟨rfl, hj.trans hi.symm,
          (mem_gridH R (i + 1) r).mpr (Or.inl ⟨hi, hs⟩)⟩)
      · exact Or.inl ⟨rfl, hj.trans hi.symm,
          (mem_gridH R i r).mpr (Or.inl ⟨hi, hs⟩)⟩

theorem gridCompletion_unique {w : ℕ} {S : State 3} (R : GridMatching w S)
    (r : Fin 3) (i : ℕ) (hi : i < w) : ∃! b, GridCompletion R (r, i) b := by
  by_cases hole : i + 1 = w ∧ r ∈ S
  · refine ⟨(r, w), Or.inr ⟨rfl, hole.2, Or.inl ⟨hole.1, rfl⟩⟩, ?_⟩
    intro b hb
    rcases hb with hb | ⟨hr, _, ⟨_, hc⟩ | ⟨_, hc⟩⟩
    · exact (((R.live (r, i)).mp ⟨b, hb⟩).2 hole).elim
    · exact Prod.ext hr.symm hc
    · dsimp only at hc
      omega
  · obtain ⟨b, hb⟩ := (R.live (r, i)).mpr ⟨hi, hole⟩
    refine ⟨b, Or.inl hb, ?_⟩
    intro c hc
    rcases hc with hc | ⟨_, hs, ⟨hh, _⟩ | ⟨_, hh⟩⟩
    · exact R.unique _ _ _ hc hb
    · exact (hole ⟨hh, hs⟩).elim
    · dsimp only at hh
      omega

noncomputable def frameOfGrid {w : ℕ} {S : State 3} (R : GridMatching w S) : ColumnFrame w S where
  horizontal := gridH R
  vertical := gridV R
  start := gridH_start R
  finish := gridH_finish R
  hsupport := gridH_support R
  vsupport := gridV_support R
  column i hi := by
    apply (columnRule_iff_unique_neighbors _ _ (gridH_start R) i).mpr
    intro r
    exact (existsUnique_congr (gridLink_extract_iff R (r, i))).mpr (gridCompletion_unique R r i hi)

theorem grid_frame_roundtrip {w : ℕ} {S : State 3} (R : GridMatching w S) :
    gridOfFrame (frameOfGrid R) = R := by
  apply gridMatching_ext
  intro a b
  change (a.2 < w ∧ b.2 < w ∧ GridLink (gridH R) (gridV R) a b) ↔ R.rel a b
  rw [gridLink_extract_iff]
  constructor
  · rintro ⟨ha, hb, h | ⟨_, _, ⟨_, he⟩ | ⟨_, he⟩⟩⟩
    · exact h
    · omega
    · omega
  · intro h
    exact ⟨(grid_matching_bounds R h).1, (grid_matching_bounds R h).2, Or.inl h⟩

theorem frame_horizontal_roundtrip {w : ℕ} {S : State 3} (F : ColumnFrame w S) :
    gridH (gridOfFrame F) = F.horizontal := by
  funext k
  ext r
  rw [mem_gridH]
  constructor
  · rintro (⟨rfl, hr⟩ | ⟨j, hj, h⟩)
    · simpa [F.finish] using hr
    · have hlink := h.2.2
      have : GridLink F.horizontal F.vertical (r, j) (r, j + 1) := by simpa [hj] using hlink
      simpa [hj] using (gridLink_horizontal _ _ r j).mp this
  · intro hr
    by_cases hk : k = w
    · exact Or.inl ⟨hk, by simpa [hk, F.finish] using hr⟩
    · have hle := frame_hbound F hr
      have hpos : 0 < k := by
        by_contra hz
        have : k = 0 := by omega
        simp [this, F.start] at hr
      have hp : k - 1 + 1 = k := by omega
      refine Or.inr ⟨k - 1, hp, ?_⟩
      refine ⟨by dsimp; omega, by dsimp; omega, ?_⟩
      have hlink := (gridLink_horizontal F.horizontal F.vertical r (k - 1)).mpr
        (by simpa [hp] using hr)
      simpa [hp] using hlink

theorem frame_vertical_roundtrip {w : ℕ} {S : State 3} (F : ColumnFrame w S) :
    gridV (gridOfFrame F) = F.vertical := by
  funext k
  by_cases hk : k < w
  · ext r
    fin_cases r <;> simp [mem_gridV, gridOfFrame, hk]
  · rw [gridV_support _ k (by omega), F.vsupport k (by omega)]

theorem frame_grid_roundtrip {w : ℕ} {S : State 3} (F : ColumnFrame w S) :
    frameOfGrid (gridOfFrame F) = F := by
  exact columnFrame_ext _ _ (frame_horizontal_roundtrip F) (frame_vertical_roundtrip F)

noncomputable def gridEquivFrame (w : ℕ) (S : State 3) :
    GridMatching w S ≃ ColumnFrame w S where
  toFun := frameOfGrid
  invFun := gridOfFrame
  left_inv := grid_frame_roundtrip
  right_inv := frame_grid_roundtrip

noncomputable def partialEquivFrame (w : ℕ) (S : State 3) :
    PartialTiling 3 w S ≃ ColumnFrame w S := (partialEquivGrid w S).trans (gridEquivFrame w S)

end Domino
