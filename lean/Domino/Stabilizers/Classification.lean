module

public import Domino.ThreeRows.Recurrence
public import Mathlib.Data.Fintype.Sum

/-! M7：三行铺法的精确稳定子。类型 0,1,2,3,4 分别为全群、仅 h、仅 v、仅 rho、平凡。 -/

@[expose] public section

namespace Domino

theorem horizontal_fixed_all {n : ℕ} (T : Tiling 3 (2 * n))
    (hT : horizontal • T = T) (g : RectangleSymmetry) : g • T = T := by
  have hh : horizontal • (g • T) = g • T := by rw [smul_comm, hT]
  exact (horizontal_fixed_unique n _ hh).trans (horizontal_fixed_unique n T hT).symm

theorem allHorizontal_fixed_all (n : ℕ) (g : RectangleSymmetry) :
    g • allHorizontalTiling n = allHorizontalTiling n :=
  horizontal_fixed_all _ (allHorizontalTiling_fixed n) g

theorem vertical_halfTurn_implies_horizontal {m w : ℕ} (T : Tiling m w)
    (hv : vertical • T = T) (hr : halfTurn • T = T) : horizontal • T = T := by
  have he : vertical * halfTurn = horizontal := by decide
  rw [← he, mul_smul, hr, hv]

theorem nonidentity_fixed_intersections (n : ℕ) (T : Tiling 3 (2 * n)) :
    ((horizontal • T = T ∧ vertical • T = T) ↔ T = allHorizontalTiling n) ∧
    ((horizontal • T = T ∧ halfTurn • T = T) ↔ T = allHorizontalTiling n) ∧
    ((vertical • T = T ∧ halfTurn • T = T) ↔ T = allHorizontalTiling n) := by
  have h (g : RectangleSymmetry) := allHorizontal_fixed_all n g
  refine ⟨⟨fun ht => horizontal_fixed_unique n T ht.1, ?_⟩,
    ⟨fun ht => horizontal_fixed_unique n T ht.1, ?_⟩,
    ⟨fun ht => horizontal_fixed_unique n T (vertical_halfTurn_implies_horizontal T ht.1 ht.2), ?_⟩⟩
  all_goals rintro rfl; exact ⟨h _, h _⟩

def stabilizerElements (t : Fin 5) : Finset RectangleSymmetry :=
  ![Finset.univ, {1, horizontal}, {1, vertical}, {1, halfTurn}, {1}] t

def symmetryOrbitSize (t : Fin 5) : ℕ := ![1, 2, 2, 2, 4] t

noncomputable def symmetryKind {n : ℕ} (T : Tiling 3 (2 * n)) : Fin 5 := by
  classical
  exact if horizontal • T = T then 0 else if vertical • T = T then 2
    else if halfTurn • T = T then 3 else 4

theorem symmetryKind_fixed_iff {n : ℕ} (T : Tiling 3 (2 * n)) (g : RectangleSymmetry) :
    g • T = T ↔ g ∈ stabilizerElements (symmetryKind T) := by
  classical
  have hh := horizontal_fixed_all T
  have hvr := vertical_halfTurn_implies_horizontal T
  rcases symmetry_exhaustive g with rfl | rfl | rfl | rfl
  all_goals
    by_cases h : horizontal • T = T <;>
      by_cases v : vertical • T = T <;> by_cases r : halfTurn • T = T
    all_goals simp_all [symmetryKind, stabilizerElements]
  all_goals decide

theorem symmetryKind_ne_horizontal {n : ℕ} (T : Tiling 3 (2 * n)) : symmetryKind T ≠ 1 := by
  classical
  simp only [symmetryKind]
  split_ifs <;> decide

theorem symmetryKind_full_iff {n : ℕ} (T : Tiling 3 (2 * n)) :
    symmetryKind T = 0 ↔ horizontal • T = T := by
  classical
  simp only [symmetryKind]
  split_ifs <;> simp_all

theorem fixed_after_smul_iff {m w : ℕ} (T : Tiling m w) (g h : RectangleSymmetry) :
    h • (g • T) = g • T ↔ h • T = T := by
  rw [smul_comm, smul_left_cancel_iff]

theorem symmetryKind_smul {n : ℕ} (T : Tiling 3 (2 * n)) (g : RectangleSymmetry) :
    symmetryKind (g • T) = symmetryKind T := by
  classical
  simp only [symmetryKind, fixed_after_smul_iff]

theorem symmetryKind_orbit_invariant {n : ℕ} (T U : Tiling 3 (2 * n))
    (h : MulAction.orbitRel RectangleSymmetry (Tiling 3 (2 * n)) T U) :
    symmetryKind T = symmetryKind U := by
  obtain ⟨g, rfl⟩ := (MulAction.mem_orbit_iff.mp h)
  exact symmetryKind_smul _ _

abbrev SymmetryTilings (n : ℕ) (t : Fin 5) := {T : Tiling 3 (2 * n) // symmetryKind T = t}

noncomputable instance symmetryTilingsFintype (n : ℕ) (t : Fin 5) : Fintype (SymmetryTilings n t) :=
  Fintype.ofFinite _

noncomputable def symmetryTilingCount (n : ℕ) (t : Fin 5) : ℕ := Fintype.card (SymmetryTilings n t)

theorem exact_stabilizer (n : ℕ) (t : Fin 5) (T : SymmetryTilings n t) :
    ∀ g, g ∈ MulAction.stabilizer RectangleSymmetry T.val ↔ g ∈ stabilizerElements t := by
  intro g
  change g • T.val = T.val ↔ _
  rw [symmetryKind_fixed_iff, T.property]

theorem stabilizer_card_exact (n : ℕ) (t : Fin 5) (T : SymmetryTilings n t) :
    Nat.card (MulAction.stabilizer RectangleSymmetry T.val) = (stabilizerElements t).card := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (exact_stabilizer n t T)), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

theorem orbit_size_exact (n : ℕ) (t : Fin 5) (T : SymmetryTilings n t) :
    Nat.card (MulAction.orbit RectangleSymmetry T.val) = symmetryOrbitSize t := by
  classical
  have h : Nat.card (MulAction.orbit RectangleSymmetry T.val) *
      Nat.card (MulAction.stabilizer RectangleSymmetry T.val) = 4 := by
    rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup RectangleSymmetry T.val),
      Nat.card_eq_fintype_card]
    exact symmetry_card_four
  rw [stabilizer_card_exact n t T] at h
  have sizes : ∀ t : Fin 5, symmetryOrbitSize t * (stabilizerElements t).card = 4 := by decide
  have positive : ∀ t : Fin 5, 0 < (stabilizerElements t).card := by decide
  exact Nat.eq_of_mul_eq_mul_right (positive t) (h.trans (sizes t).symm)

noncomputable instance symmetryTilingsAction (n : ℕ) (t : Fin 5) :
    MulAction RectangleSymmetry (SymmetryTilings n t) where
  smul g T := ⟨g • T.val, (symmetryKind_smul T.val g).trans T.property⟩
  one_smul T := Subtype.ext (one_smul RectangleSymmetry T.val)
  mul_smul g h T := Subtype.ext (mul_smul g h T.val)

abbrev SymmetryOrbits (n : ℕ) (t : Fin 5) :=
  Quotient (MulAction.orbitRel RectangleSymmetry (SymmetryTilings n t))

noncomputable instance symmetryOrbitsFintype (n : ℕ) (t : Fin 5) : Fintype (SymmetryOrbits n t) :=
  Fintype.ofFinite _

noncomputable def symmetryOrbitCount (n : ℕ) (t : Fin 5) : ℕ := Fintype.card (SymmetryOrbits n t)

theorem typed_orbit_iff (n : ℕ) (t : Fin 5) (T U : SymmetryTilings n t) :
    MulAction.orbitRel RectangleSymmetry (SymmetryTilings n t) T U ↔
    MulAction.orbitRel RectangleSymmetry (Tiling 3 (2 * n)) T.val U.val := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, h⟩; exact ⟨g, congrArg Subtype.val h⟩
  · rintro ⟨g, h⟩; exact ⟨g, Subtype.ext h⟩

end Domino
