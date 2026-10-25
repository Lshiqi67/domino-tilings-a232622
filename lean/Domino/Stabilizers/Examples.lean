module

public import Domino.Stabilizers.Counts

/-! 从一般分类与既有计数递推推导空棋盘和论文 n=8 示例。 -/

@[expose] public section

namespace Domino

theorem symmetryOrbitCount_partition (n : ℕ) :
    ∑ t : Fin 5, symmetryOrbitCount n t = a n := by
  have ht := symmetryTilingCount_formulas n
  have hv := symmetryTilingCount_vertical_add n
  have hr := symmetryTilingCount_halfTurn_add n
  have hsum := symmetryTilingCount_trivial_add n
  have hb := four_mul_a n
  have h0 := symmetryOrbitCount_mul_size n 0
  have h1 := symmetryOrbitCount_mul_size n 1
  have h2 := symmetryOrbitCount_mul_size n 2
  have h3 := symmetryOrbitCount_mul_size n 3
  have h4 := symmetryOrbitCount_mul_size n 4
  norm_num [symmetryOrbitSize] at h0 h1 h2 h3 h4
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one]
  norm_num
  omega

theorem symmetry_orbit_zero :
    symmetryOrbitCount 0 0 = 1 ∧ symmetryOrbitCount 0 1 = 0 ∧
    symmetryOrbitCount 0 2 = 0 ∧ symmetryOrbitCount 0 3 = 0 ∧ symmetryOrbitCount 0 4 = 0 := by
  simpa only [fixedCount_zero, ordinaryCount_zero, Nat.sub_self, Nat.zero_div,
    Nat.reduceAdd] using symmetryOrbitCount_formulas 0

theorem symmetry_orbit_eight :
    symmetryOrbitCount 8 0 = 1 ∧ symmetryOrbitCount 8 1 = 0 ∧
    symmetryOrbitCount 8 2 = 132 ∧ symmetryOrbitCount 8 3 = 76 ∧
    symmetryOrbitCount 8 4 = 7316 ∧ a 8 = 7525 := by
  have hv : fixedCount 3 8 vertical = 265 := by
    change fixedCount 3 (2 * 4) vertical = 265
    rw [reflection_even]
    norm_num [ordinary_eq_alpha, alpha, profilePair]
  have hr : fixedCount 3 8 halfTurn = 153 := by
    change fixedCount 3 (2 * 4) halfTurn = 153
    rw [halfTurn_even]
    norm_num [ordinary_eq_alpha, alpha, profilePair]
  have hd : ordinaryCount 3 8 = 29681 := by norm_num [ordinary_eq_alpha, alpha, profilePair]
  have h := symmetryOrbitCount_formulas 8
  have hb := four_mul_a 8
  norm_num [hv, hr, hd] at h hb
  omega

theorem three_row_stabilizer_counting (n : ℕ) :
    (∀ t (T : SymmetryTilings n t),
      (∀ g, g ∈ MulAction.stabilizer RectangleSymmetry T.val ↔ g ∈ stabilizerElements t) ∧
      Nat.card (MulAction.orbit RectangleSymmetry T.val) = symmetryOrbitSize t) ∧
    (∀ t, symmetryOrbitSize t * symmetryOrbitCount n t = symmetryTilingCount n t) ∧
    (∑ t : Fin 5, symmetryOrbitCount n t) = a n :=
  ⟨fun t T => ⟨exact_stabilizer n t T, orbit_size_exact n t T⟩,
    symmetryOrbitCount_mul_size n, symmetryOrbitCount_partition n⟩

end Domino
