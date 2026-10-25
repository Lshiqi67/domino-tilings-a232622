module

public import Domino.Board.Partial
public import Mathlib.GroupTheory.GroupAction.Quotient

/-! 抽象四元群及其在格子、无序砖与完整铺法上的作用。 -/

@[expose] public section

namespace Domino

structure RectangleSymmetry where
  flipRows : Bool
  flipCols : Bool
  deriving DecidableEq, Fintype

instance rectangle_group : CommGroup RectangleSymmetry where
  mul g h := ⟨Bool.xor g.flipRows h.flipRows, Bool.xor g.flipCols h.flipCols⟩
  one := ⟨false, false⟩
  inv g := g
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide
  mul_comm := by decide

theorem symmetry_mul_def (g h : RectangleSymmetry) :
    g * h = ⟨Bool.xor g.flipRows h.flipRows, Bool.xor g.flipCols h.flipCols⟩ := rfl

theorem symmetry_one_def : (1 : RectangleSymmetry) = ⟨false, false⟩ := rfl

def horizontal : RectangleSymmetry := ⟨true, false⟩
def vertical : RectangleSymmetry := ⟨false, true⟩
def halfTurn : RectangleSymmetry := ⟨true, true⟩

theorem symmetry_card_four : Fintype.card RectangleSymmetry = 4 := by decide
theorem horizontal_mul_vertical : horizontal * vertical = halfTurn := by decide

theorem symmetry_exhaustive (g : RectangleSymmetry) :
    g = 1 ∨ g = horizontal ∨ g = vertical ∨ g = halfTurn := by
  rcases g with ⟨a, b⟩
  cases a <;> cases b <;> decide

def cellAction {m w : ℕ} (g : RectangleSymmetry) (c : Cell m w) : Cell m w :=
  (if g.flipRows then c.1.rev else c.1, if g.flipCols then c.2.rev else c.2)

@[simp] theorem cellAction_one {m w : ℕ} (c : Cell m w) : cellAction 1 c = c := by
  simp [cellAction, symmetry_one_def]

@[simp] theorem cellAction_twice {m w : ℕ} (g : RectangleSymmetry) (c : Cell m w) :
    cellAction g (cellAction g c) = c := by
  rcases g with ⟨a, b⟩
  cases a <;> cases b <;> simp [cellAction]

theorem cellAction_mul {m w : ℕ} (g h : RectangleSymmetry) (c : Cell m w) :
    cellAction (g * h) c = cellAction g (cellAction h c) := by
  rcases g with ⟨a, b⟩
  rcases h with ⟨c', d⟩
  cases a <;> cases b <;> cases c' <;> cases d <;>
    simp [cellAction, symmetry_mul_def]

theorem cellAction_horizontal {m w : ℕ} (c : Cell m w) :
    cellAction horizontal c = reflectRows c := rfl

theorem cellAction_vertical {m w : ℕ} (c : Cell m w) :
    cellAction vertical c = reflectCols c := rfl

theorem cellAction_halfTurn {m w : ℕ} (c : Cell m w) :
    cellAction halfTurn c = reflectRows (reflectCols c) := rfl

theorem cellAction_adjacent_iff {m w : ℕ} (g : RectangleSymmetry) (a b : Cell m w) :
    Adjacent (cellAction g a) (cellAction g b) ↔ Adjacent a b := by
  rcases g with ⟨x, y⟩
  cases x <;> cases y
  · rfl
  · exact adjacent_reflectCols_iff a b
  · exact adjacent_reflectRows_iff a b
  · exact (adjacent_reflectRows_iff (reflectCols a) (reflectCols b)).trans
      (adjacent_reflectCols_iff a b)

def cellPerm {m w : ℕ} (g : RectangleSymmetry) : Equiv.Perm (Cell m w) where
  toFun := cellAction g
  invFun := cellAction g
  left_inv := cellAction_twice g
  right_inv := cellAction_twice g

def edgeAction {m w : ℕ} (g : RectangleSymmetry) (e : Edge m w) : Edge m w :=
  ⟨e.val.map (cellPerm g).toEmbedding, by
    obtain ⟨a, b, hab, he⟩ := e.property
    refine ⟨cellAction g a, cellAction g b, (cellAction_adjacent_iff g a b).mpr hab, ?_⟩
    simp [he, cellPerm]⟩

@[simp] theorem mem_edgeAction {m w : ℕ} (g : RectangleSymmetry)
    (e : Edge m w) (c : Cell m w) :
    c ∈ (edgeAction g e).val ↔ cellAction g c ∈ e.val :=
  Finset.mem_map_equiv

@[simp] theorem edgeAction_twice {m w : ℕ} (g : RectangleSymmetry) (e : Edge m w) :
    edgeAction g (edgeAction g e) = e := by
  apply Subtype.ext
  ext c
  simp only [mem_edgeAction, cellAction_twice]

@[simp] theorem edgeAction_one {m w : ℕ} (e : Edge m w) : edgeAction 1 e = e := by
  apply Subtype.ext
  ext c
  simp only [mem_edgeAction, cellAction_one]

theorem edgeAction_mul {m w : ℕ} (g h : RectangleSymmetry) (e : Edge m w) :
    edgeAction (g * h) e = edgeAction g (edgeAction h e) := by
  apply Subtype.ext
  ext c
  simp only [mem_edgeAction]
  rw [← cellAction_mul, mul_comm h g]

def edgePerm {m w : ℕ} (g : RectangleSymmetry) : Equiv.Perm (Edge m w) where
  toFun := edgeAction g
  invFun := edgeAction g
  left_inv := edgeAction_twice g
  right_inv := edgeAction_twice g

def mapEdges {m w : ℕ} (g : RectangleSymmetry) (E : Finset (Edge m w)) :=
  E.map (edgePerm g).toEmbedding

def mapHoles {m w : ℕ} (g : RectangleSymmetry) (H : Finset (Cell m w)) :=
  H.map (cellPerm g).toEmbedding

@[simp] theorem mem_mapEdges {m w : ℕ} (g : RectangleSymmetry)
    (E : Finset (Edge m w)) (e : Edge m w) :
    e ∈ mapEdges g E ↔ edgeAction g e ∈ E := Finset.mem_map_equiv

@[simp] theorem mem_mapHoles {m w : ℕ} (g : RectangleSymmetry)
    (H : Finset (Cell m w)) (c : Cell m w) :
    c ∈ mapHoles g H ↔ cellAction g c ∈ H := Finset.mem_map_equiv

@[simp] theorem mapEdges_one {m w : ℕ} (E : Finset (Edge m w)) : mapEdges 1 E = E := by
  ext e
  simp only [mem_mapEdges, edgeAction_one]

theorem mapEdges_mul {m w : ℕ} (g h : RectangleSymmetry) (E : Finset (Edge m w)) :
    mapEdges (g * h) E = mapEdges g (mapEdges h E) := by
  ext e
  simp only [mem_mapEdges]
  rw [← edgeAction_mul, mul_comm h g]

theorem isCover_map {m w : ℕ} (g : RectangleSymmetry)
    {H : Finset (Cell m w)} {E : Finset (Edge m w)} (h : IsCover H E) :
    IsCover (mapHoles g H) (mapEdges g E) := by
  constructor
  · intro c
    constructor
    · rintro ⟨e, he, hc⟩
      have hce : cellAction g c ∈ (edgeAction g e).val := by simpa using hc
      have hH := (h.1 (cellAction g c)).mp ⟨edgeAction g e, (mem_mapEdges g E e).mp he, hce⟩
      simpa only [mem_mapHoles] using hH
    · intro hc
      have hH : cellAction g c ∉ H := by simpa only [mem_mapHoles] using hc
      obtain ⟨e, he, hce⟩ := (h.1 (cellAction g c)).mpr hH
      exact ⟨edgeAction g e, by simpa using he, (mem_edgeAction g e c).mpr hce⟩
  · intro e he f hf c hce hcf
    apply (edgePerm g).injective
    exact h.2 (edgeAction g e) ((mem_mapEdges g E e).mp he)
      (edgeAction g f) ((mem_mapEdges g E f).mp hf) (cellAction g c)
      (by simpa using hce) (by simpa using hcf)

def tilingAction {m w : ℕ} (g : RectangleSymmetry) (T : Tiling m w) : Tiling m w :=
  ⟨mapEdges g T.val, by simpa [mapHoles] using isCover_map g T.property⟩

instance rectangle_action (m w : ℕ) : MulAction RectangleSymmetry (Tiling m w) where
  smul := tilingAction
  one_smul T := Subtype.ext (mapEdges_one T.val)
  mul_smul g h T := Subtype.ext (mapEdges_mul g h T.val)

theorem smul_edges {m w : ℕ} (g : RectangleSymmetry) (T : Tiling m w) :
    (g • T).val = mapEdges g T.val := rfl

theorem empty_tiling_action (m : ℕ) (g : RectangleSymmetry) (T : Tiling m 0) :
    g • T = T := Subsingleton.elim _ _

end Domino
