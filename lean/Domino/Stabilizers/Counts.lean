module

public import Domino.Stabilizers.Classification

/-! M7：各精确稳定子类型的真实铺法数与商集基数。先证明无减法恒等式，再导出商和整除性。 -/

@[expose] public section

namespace Domino

theorem symmetryTilingCount_full (n : ℕ) : symmetryTilingCount n 0 = 1 := by
  classical
  let _ : Unique (SymmetryTilings n 0) :=
    { default := ⟨allHorizontalTiling n, (symmetryKind_full_iff _).mpr (allHorizontalTiling_fixed n)⟩
      uniq := fun T => Subtype.ext (horizontal_fixed_unique n T.val ((symmetryKind_full_iff _).mp T.property)) }
  exact Fintype.card_unique

theorem symmetryTilingCount_horizontal (n : ℕ) : symmetryTilingCount n 1 = 0 := by
  classical
  let _ : IsEmpty (SymmetryTilings n 1) := ⟨fun T => symmetryKind_ne_horizontal T.val T.property⟩
  exact Fintype.card_of_isEmpty

theorem fixed_iff_kind (n : ℕ) (g : RectangleSymmetry) (T : Tiling 3 (2 * n)) :
    g • T = T ↔ g ∈ stabilizerElements (symmetryKind T) := symmetryKind_fixed_iff T g

theorem reflection_fixed_iff_kind (n : ℕ) (T : Tiling 3 (2 * n)) :
    vertical • T = T ↔ symmetryKind T = 0 ∨ symmetryKind T = 2 := by
  rw [symmetryKind_fixed_iff]
  generalize symmetryKind T = k
  fin_cases k <;> decide

theorem halfTurn_fixed_iff_kind (n : ℕ) (T : Tiling 3 (2 * n)) :
    halfTurn • T = T ↔ symmetryKind T = 0 ∨ symmetryKind T = 3 := by
  rw [symmetryKind_fixed_iff]
  generalize symmetryKind T = k
  fin_cases k <;> decide

theorem kind_union_card (n : ℕ) (i j : Fin 5) (hij : i ≠ j) :
    Fintype.card {T : Tiling 3 (2 * n) // symmetryKind T = i ∨ symmetryKind T = j} =
      symmetryTilingCount n i + symmetryTilingCount n j := by
  classical
  apply Fintype.card_subtype_or_disjoint
  exact fun _ hi hj _ hT => hij ((hi _ hT).symm.trans (hj _ hT))

theorem symmetryTilingCount_vertical_add (n : ℕ) :
    symmetryTilingCount n 2 + 1 = fixedCount 3 n vertical := by
  classical
  have h := Fintype.card_congr (Equiv.subtypeEquivRight (reflection_fixed_iff_kind n))
  rw [kind_union_card n 0 2 (by decide), symmetryTilingCount_full] at h
  change fixedCount 3 n vertical = _ at h
  omega

theorem symmetryTilingCount_halfTurn_add (n : ℕ) :
    symmetryTilingCount n 3 + 1 = fixedCount 3 n halfTurn := by
  classical
  have h := Fintype.card_congr (Equiv.subtypeEquivRight (halfTurn_fixed_iff_kind n))
  rw [kind_union_card n 0 3 (by decide), symmetryTilingCount_full] at h
  change fixedCount 3 n halfTurn = _ at h
  omega

theorem symmetryTilingCount_partition (n : ℕ) :
    ∑ t : Fin 5, symmetryTilingCount n t = ordinaryCount 3 n := by
  classical
  exact (Fintype.card_sigma).symm.trans (Fintype.card_congr (Equiv.sigmaFiberEquiv (@symmetryKind n)))

theorem symmetryTilingCount_trivial_add (n : ℕ) :
    symmetryTilingCount n 4 + fixedCount 3 n vertical + fixedCount 3 n halfTurn =
      ordinaryCount 3 n + 1 := by
  have h := symmetryTilingCount_partition n
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one] at h
  have hf := symmetryTilingCount_full n
  have hh := symmetryTilingCount_horizontal n
  have hv := symmetryTilingCount_vertical_add n
  have hr := symmetryTilingCount_halfTurn_add n
  norm_num at h
  omega

theorem symmetryTilingCount_formulas (n : ℕ) :
    symmetryTilingCount n 0 = 1 ∧ symmetryTilingCount n 1 = 0 ∧
    symmetryTilingCount n 2 = fixedCount 3 n vertical - 1 ∧
    symmetryTilingCount n 3 = fixedCount 3 n halfTurn - 1 ∧
    symmetryTilingCount n 4 = ordinaryCount 3 n + 1 -
      (fixedCount 3 n vertical + fixedCount 3 n halfTurn) := by
  have hv := symmetryTilingCount_vertical_add n
  have hr := symmetryTilingCount_halfTurn_add n
  have ht := symmetryTilingCount_trivial_add n
  exact ⟨symmetryTilingCount_full n, symmetryTilingCount_horizontal n, by omega, by omega, by omega⟩

theorem typed_fixed_card (n : ℕ) (t : Fin 5) (g : RectangleSymmetry) :
    Nat.card (MulAction.fixedBy (SymmetryTilings n t) g) =
      if g ∈ stabilizerElements t then symmetryTilingCount n t else 0 := by
  classical
  have h (T : SymmetryTilings n t) : g • T = T ↔ g ∈ stabilizerElements t := by
    rw [Subtype.ext_iff]
    exact (symmetryKind_fixed_iff T.val g).trans (by rw [T.property])
  change Nat.card {T : SymmetryTilings n t // g • T = T} = _
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card]
  by_cases hg : g ∈ stabilizerElements t <;> simp [hg, symmetryTilingCount]

theorem symmetryOrbitCount_mul_size (n : ℕ) (t : Fin 5) :
    symmetryOrbitSize t * symmetryOrbitCount n t = symmetryTilingCount n t := by
  classical
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group RectangleSymmetry (SymmetryTilings n t)
  have ho : Fintype.card (Quotient (MulAction.orbitRel RectangleSymmetry (SymmetryTilings n t))) =
      symmetryOrbitCount n t := Fintype.card_congr (Equiv.refl _)
  have hf (g : RectangleSymmetry) : Fintype.card (MulAction.fixedBy (SymmetryTilings n t) g) =
      if g ∈ stabilizerElements t then symmetryTilingCount n t else 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact typed_fixed_card n t g
  simp only [hf, ho, symmetry_card_four] at h
  have hs : (∑ g : RectangleSymmetry, if g ∈ stabilizerElements t then symmetryTilingCount n t else 0) =
      (stabilizerElements t).card * symmetryTilingCount n t := by
    rw [← Finset.sum_filter]
    simp
  rw [hs] at h
  have sizes : ∀ t : Fin 5, symmetryOrbitSize t * (stabilizerElements t).card = 4 := by decide
  have positive : ∀ t : Fin 5, 0 < (stabilizerElements t).card := by decide
  apply Nat.eq_of_mul_eq_mul_left (positive t)
  calc
    (stabilizerElements t).card * (symmetryOrbitSize t * symmetryOrbitCount n t) =
        (symmetryOrbitSize t * (stabilizerElements t).card) * symmetryOrbitCount n t := by ring
    _ = 4 * symmetryOrbitCount n t := by rw [sizes]
    _ = (stabilizerElements t).card * symmetryTilingCount n t := by omega

theorem symmetryOrbitCount_formulas (n : ℕ) :
    symmetryOrbitCount n 0 = 1 ∧ symmetryOrbitCount n 1 = 0 ∧
    symmetryOrbitCount n 2 = (fixedCount 3 n vertical - 1) / 2 ∧
    symmetryOrbitCount n 3 = (fixedCount 3 n halfTurn - 1) / 2 ∧
    symmetryOrbitCount n 4 = (ordinaryCount 3 n + 1 -
      (fixedCount 3 n vertical + fixedCount 3 n halfTurn)) / 4 := by
  have ht := symmetryTilingCount_formulas n
  have h0 := symmetryOrbitCount_mul_size n 0
  have h1 := symmetryOrbitCount_mul_size n 1
  have h2 := symmetryOrbitCount_mul_size n 2
  have h3 := symmetryOrbitCount_mul_size n 3
  have h4 := symmetryOrbitCount_mul_size n 4
  norm_num [symmetryOrbitSize] at h0 h1 h2 h3 h4
  omega

theorem symmetry_type_divisibility (n : ℕ) :
    2 ∣ fixedCount 3 n vertical - 1 ∧ 2 ∣ fixedCount 3 n halfTurn - 1 ∧
    4 ∣ ordinaryCount 3 n + 1 - (fixedCount 3 n vertical + fixedCount 3 n halfTurn) := by
  have ht := symmetryTilingCount_formulas n
  exact ⟨⟨symmetryOrbitCount n 2, ht.2.2.1.symm.trans (symmetryOrbitCount_mul_size n 2).symm⟩,
    ⟨symmetryOrbitCount n 3, ht.2.2.2.1.symm.trans (symmetryOrbitCount_mul_size n 3).symm⟩,
    ⟨symmetryOrbitCount n 4, ht.2.2.2.2.symm.trans (symmetryOrbitCount_mul_size n 4).symm⟩⟩

end Domino
