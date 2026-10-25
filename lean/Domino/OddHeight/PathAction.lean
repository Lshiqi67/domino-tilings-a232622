module

public import Domino.OddHeight.Count
public import Domino.Symmetry.PathAction
public import Domino.OddHeight.ColumnSymmetry

/-! 任意高度：坐标反射在几何切口路径上的作用。 -/

@[expose] public section

namespace Domino.General

variable {m : ℕ}

noncomputable def tilingPath {w : ℕ} (T : Tiling m w) : StatePath (m := m) w ∅ :=
  tilingEquivClosedPath w T

theorem tilingPath_state {w : ℕ} (T : Tiling m w) (k : ℕ) :
    (tilingPath T).state k = gridH (gridOfPartial ((partialEmptyEquivTiling m w).symm T)) k := rfl

theorem tilingPath_cut {w : ℕ} (T : Tiling m w) (k : ℕ) (hk : 0 < k) (hkw : k < w)
    (r : Fin m) :
    r ∈ (tilingPath T).state k ↔
      ((r, ⟨k - 1, by omega⟩), (r, ⟨k, hkw⟩)) ∈ coverBonds T := by
  rw [tilingPath_state, mem_gridH]
  simp only [Finset.notMem_empty, and_false, false_or]
  constructor
  · rintro ⟨j, hj, ha, hb, h⟩
    have he : j = k - 1 := by omega
    subst j
    exact h
  · intro h
    exact ⟨k - 1, by omega, by omega, hkw, h⟩

theorem tilingPath_horizontal {w : ℕ} (T : Tiling m w) (k : ℕ) :
    (tilingPath (horizontal • T)).state k = reverseState ((tilingPath T).state k) := by
  by_cases hz : k = 0
  · subst k
    simp [(tilingPath _).start]
  by_cases he : k = w
  · subst k
    simp [(tilingPath _).finish]
  by_cases hk : k < w
  · ext r
    rw [mem_reverseState, tilingPath_cut _ k (by omega) hk,
      tilingPath_cut _ k (by omega) hk, coverBonds_action]
    rfl
  · rw [(tilingPath _).support k (by omega), (tilingPath _).support k (by omega)]
    rfl

theorem tilingPath_vertical {w : ℕ} (T : Tiling m w) (k : ℕ) (hk : k ≤ w) :
    (tilingPath (vertical • T)).state k = (tilingPath T).state (w - k) := by
  by_cases hz : k = 0
  · subst k
    simp [(tilingPath _).start, (tilingPath _).finish]
  by_cases he : k = w
  · subst k
    simp [(tilingPath _).start, (tilingPath _).finish]
  have hi : k < w := by omega
  have hj : w - k < w := by omega
  ext r
  rw [tilingPath_cut _ k (by omega) hi, tilingPath_cut _ (w - k) (by omega) hj,
    coverBonds_action]
  have hleft : cellAction vertical (r, (⟨k - 1, by omega⟩ : Fin w)) =
      (r, (⟨w - k, hj⟩ : Fin w)) := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp only [cellAction, vertical, Bool.false_eq_true, ↓reduceIte, Fin.val_rev]
      omega
  have hright : cellAction vertical (r, (⟨k, hi⟩ : Fin w)) =
      (r, (⟨w - k - 1, by omega⟩ : Fin w)) := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp only [cellAction, vertical, Bool.false_eq_true, ↓reduceIte, Fin.val_rev]
      omega
  rw [hleft, hright]
  exact ⟨(coverBonds_valid T).2.1 _ _, (coverBonds_valid T).2.1 _ _⟩

theorem tilingPath_halfTurn {w : ℕ} (T : Tiling m w) (k : ℕ) (hk : k ≤ w) :
    (tilingPath (halfTurn • T)).state k = reverseState ((tilingPath T).state (w - k)) := by
  rw [← horizontal_mul_vertical, mul_smul, tilingPath_horizontal, tilingPath_vertical T k hk]

theorem horizontal_fixed_iff_path {w : ℕ} (T : Tiling m w) :
    horizontal • T = T ↔ ∀ k, reverseState ((tilingPath T).state k) = (tilingPath T).state k := by
  constructor
  · intro h k
    rw [← tilingPath_horizontal, h]
  · intro h
    apply (tilingEquivClosedPath w).injective
    apply statePath_ext
    funext k
    exact (tilingPath_horizontal T k).trans (h k)

def twistState (b : Bool) (S : State m) : State m := if b then reverseState S else S

@[simp] theorem twistState_twice (b : Bool) (S : State m) :
    twistState b (twistState b S) = S := by cases b <;> simp [twistState]

@[simp] theorem twistState_empty (b : Bool) : twistState b (∅ : State m) = ∅ := by
  cases b <;> simp [twistState]

def axialSymmetry (b : Bool) : RectangleSymmetry := ⟨b, true⟩

theorem axial_fixed_iff_path {w : ℕ} (b : Bool) (T : Tiling m w) :
    axialSymmetry b • T = T ↔
      ∀ k, k ≤ w → (tilingPath T).state k = twistState b ((tilingPath T).state (w - k)) := by
  have compat (k : ℕ) (hk : k ≤ w) :
      (tilingPath (axialSymmetry b • T)).state k = twistState b ((tilingPath T).state (w - k)) := by
    cases b
    · exact tilingPath_vertical T k hk
    · exact tilingPath_halfTurn T k hk
  constructor
  · intro h k hk
    exact (congrArg (fun T => (tilingPath T).state k) h).symm.trans (compat k hk)
  · intro h
    apply (tilingEquivClosedPath w).injective
    apply statePath_ext
    funext k
    by_cases hk : k ≤ w
    · exact (compat k hk).trans (h k hk).symm
    · exact ((tilingEquivClosedPath w (axialSymmetry b • T)).support k (by omega)).trans
        ((tilingEquivClosedPath w T).support k (by omega)).symm

end Domino.General
