module

public import Domino.Symmetry.Action
public import Mathlib.Data.Fintype.Quotient

/-! 轨道数与固定点数按实际几何铺法定义，尚未使用 Burnside 或任何递推。 -/

@[expose] public section

namespace Domino

abbrev TilingOrbit (m w : ℕ) := Quotient (MulAction.orbitRel RectangleSymmetry (Tiling m w))

noncomputable instance tilingOrbitFintype (m w : ℕ) : Fintype (TilingOrbit m w) := Fintype.ofFinite _

noncomputable def ordinaryCount (m n : ℕ) : ℕ := Fintype.card (Tiling m (2 * n))

noncomputable def orbitCount (m n : ℕ) : ℕ := Fintype.card (TilingOrbit m (2 * n))

noncomputable def fixedCount (m n : ℕ) (g : RectangleSymmetry) : ℕ := by
  classical
  exact Fintype.card {T : Tiling m (2 * n) // g • T = T}

noncomputable def a (n : ℕ) : ℕ := orbitCount 3 n

theorem orbitRel_iff_four {m w : ℕ} (T U : Tiling m w) :
    MulAction.orbitRel RectangleSymmetry (Tiling m w) T U ↔
      T = U ∨ T = horizontal • U ∨ T = vertical • U ∨ T = halfTurn • U := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    rcases symmetry_exhaustive g with rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa using hg.symm)
    · exact Or.inr (Or.inl hg.symm)
    · exact Or.inr (Or.inr (Or.inl hg.symm))
    · exact Or.inr (Or.inr (Or.inr hg.symm))
  · rintro (h | h | h | h)
    · exact ⟨1, by simpa using h.symm⟩
    · exact ⟨horizontal, h.symm⟩
    · exact ⟨vertical, h.symm⟩
    · exact ⟨halfTurn, h.symm⟩

theorem odd_height_ne_even_width (k n : ℕ) : 2 * k + 1 ≠ 2 * n := by omega

theorem three_ne_even_width (n : ℕ) : 3 ≠ 2 * n := by omega

instance tilingOrbitWidthZeroUnique (m : ℕ) : Unique (TilingOrbit m 0) where
  default := Quotient.mk _ (emptyWidthTiling m)
  uniq q := by
    refine Quotient.inductionOn q ?_
    intro T
    exact congrArg (Quotient.mk _) (empty_tiling_unique m T)

@[simp] theorem ordinaryCount_zero (m : ℕ) : ordinaryCount m 0 = 1 := by
  simp [ordinaryCount]

@[simp] theorem orbitCount_zero (m : ℕ) : orbitCount m 0 = 1 := by
  simp [orbitCount, Fintype.card_unique]

@[simp] theorem a_zero : a 0 = 1 := orbitCount_zero 3

@[simp] theorem fixedCount_zero (m : ℕ) (g : RectangleSymmetry) : fixedCount m 0 g = 1 := by
  classical
  let _ : Unique {T : Tiling m 0 // g • T = T} :=
    { default := ⟨emptyWidthTiling m, empty_tiling_action m g _⟩
      uniq := fun T => Subtype.ext (Subsingleton.elim _ _) }
  simpa only [fixedCount, Nat.mul_zero] using
    (Fintype.card_unique : Fintype.card {T : Tiling m 0 // g • T = T} = 1)

end Domino
