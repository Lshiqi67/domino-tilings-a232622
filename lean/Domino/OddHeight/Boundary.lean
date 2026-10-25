module

public import Domino.OddHeight.Series
public import Domino.OddHeight.TopGeometry

@[expose] public section

namespace Domino.General

theorem horizontal_one_row {w : ℕ} (T : Tiling 1 w) : horizontal • T = T := by
  have hc (a : Cell 1 w) : cellAction horizontal a = a := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  apply (coverEquivBonds 1 w ∅).injective
  apply Subtype.ext
  change coverBonds (horizontal • T) = coverBonds T
  ext ab
  rcases ab with ⟨a, b⟩
  rw [coverBonds_action, hc, hc]

noncomputable def oneRowEquivEmpty (n : ℕ) : Tiling 1 (2 * n) ≃ Tiling 0 (2 * n) :=
  (Equiv.subtypeUnivEquiv (horizontal_one_row (w := 2 * n))).symm.trans
    (horizontalFixedEquivTop 0 n)

theorem ordinary_one_row (n : ℕ) : ordinaryCount 1 n = 1 := by
  change Fintype.card (Tiling 1 (2 * n)) = 1
  rw [Fintype.card_congr (oneRowEquivEmpty n), tiling_card_height_zero]

theorem fixed_one_row (n : ℕ) (g : RectangleSymmetry) : fixedCount 1 n g = 1 := by
  classical
  let : Unique (Tiling 1 (2 * n)) := (oneRowEquivEmpty n).unique
  have h (T : Tiling 1 (2 * n)) : g • T = T := Subsingleton.elim _ _
  exact (Fintype.card_congr (Equiv.subtypeUnivEquiv h)).trans (ordinary_one_row n)

theorem orbit_one_row (n : ℕ) : orbitCount 1 n = 1 := by
  have h := four_mul_orbitCount 1 n
  rw [ordinary_one_row, fixed_one_row, fixed_one_row, fixed_one_row] at h
  omega

theorem zero_height_matrix_powers (n : ℕ) : (transferMatrix (m := 0) ^ n) ∅ ∅ = 1 := by
  rw [zero_height_transfer, one_pow]
  simp

theorem odd_height_main (k n : ℕ) :
    (4 * orbitCount (2 * k + 1) n =
      (transferMatrix (m := 2 * k + 1) ^ (2 * n)) ∅ ∅ +
      (transferMatrix (m := k) ^ (2 * n)) ∅ ∅ +
      (∑ S : State (2 * k + 1), (transferMatrix ^ n) ∅ S) +
      (∑ S : SymmetricTerminal (2 * k + 1), (transferMatrix ^ n) ∅ S.val)) ∧
    RationalSeries (orbitSeries k) :=
  ⟨odd_height_four_counts k n, odd_height_orbit_rational k⟩

end Domino.General
