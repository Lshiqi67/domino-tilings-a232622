module

public import Domino.Stabilizers.Examples

/-! 两个有限均匀抽样空间：真实铺法与真实轨道。 -/

@[expose] public section

namespace Domino.Asymptotic

def HasSymmetry {n : ℕ} (T : Tiling 3 (2 * n)) : Prop :=
  ∃ g : RectangleSymmetry, g ≠ 1 ∧ g • T = T

theorem hasSymmetry_iff_kind {n : ℕ} (T : Tiling 3 (2 * n)) :
    HasSymmetry T ↔ symmetryKind T ≠ 4 := by
  simp only [HasSymmetry, symmetryKind_fixed_iff]
  generalize symmetryKind T = k
  fin_cases k <;> decide

theorem hasSymmetry_smul {n : ℕ} (T : Tiling 3 (2 * n)) (g : RectangleSymmetry) :
    HasSymmetry (g • T) ↔ HasSymmetry T := by
  simp only [hasSymmetry_iff_kind, symmetryKind_smul]

abbrev SymmetricTilings (n : ℕ) := {T : Tiling 3 (2 * n) // HasSymmetry T}
noncomputable instance symmetricTilingsFintype (n : ℕ) : Fintype (SymmetricTilings n) := Fintype.ofFinite _
noncomputable def symmetricCount (n : ℕ) : ℕ := Fintype.card (SymmetricTilings n)

theorem symmetric_count_complement (n : ℕ) :
    symmetricCount n + symmetryTilingCount n 4 = ordinaryCount 3 n := by
  classical
  rw [symmetricCount, Fintype.card_congr (Equiv.subtypeEquivRight (@hasSymmetry_iff_kind n))]
  change Fintype.card {T : Tiling 3 (2 * n) // symmetryKind T ≠ 4} +
    Fintype.card {T : Tiling 3 (2 * n) // symmetryKind T = 4} = Fintype.card (Tiling 3 (2 * n))
  rw [Fintype.card_subtype_compl]
  exact Nat.sub_add_cancel (Fintype.card_subtype_le _)

theorem symmetric_count_add_one (n : ℕ) :
    symmetricCount n + 1 = fixedCount 3 n vertical + fixedCount 3 n halfTurn := by
  have hc := symmetric_count_complement n
  have ht := symmetryTilingCount_trivial_add n
  omega

noncomputable instance symmetricTilingsAction (n : ℕ) : MulAction RectangleSymmetry (SymmetricTilings n) where
  smul g T := ⟨g • T.val, (hasSymmetry_smul T.val g).2 T.property⟩
  one_smul T := Subtype.ext (one_smul RectangleSymmetry T.val)
  mul_smul g h T := Subtype.ext (mul_smul g h T.val)

abbrev SymmetricOrbits (n : ℕ) := Quotient (MulAction.orbitRel RectangleSymmetry (SymmetricTilings n))
noncomputable instance symmetricOrbitsFintype (n : ℕ) : Fintype (SymmetricOrbits n) := Fintype.ofFinite _
noncomputable def symmetricOrbitCount (n : ℕ) : ℕ := Fintype.card (SymmetricOrbits n)

theorem symmetric_orbit_relation (n : ℕ) (T U : SymmetricTilings n) :
    MulAction.orbitRel RectangleSymmetry (SymmetricTilings n) T U ↔
      MulAction.orbitRel RectangleSymmetry (Tiling 3 (2 * n)) T.val U.val := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, h⟩; exact ⟨g, congrArg Subtype.val h⟩
  · rintro ⟨g, h⟩; exact ⟨g, Subtype.ext h⟩

noncomputable def symmetricOrbitInclusion (n : ℕ) : SymmetricOrbits n → TilingOrbit 3 (2 * n) :=
  Quotient.map Subtype.val (fun _ _ h => (symmetric_orbit_relation n _ _).1 h)

theorem symmetricOrbitInclusion_injective (n : ℕ) : Function.Injective (symmetricOrbitInclusion n) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro T U h
  exact Quotient.sound ((symmetric_orbit_relation n T U).2 (Quotient.exact h))

theorem symmetricOrbitInclusion_image (n : ℕ) (O : TilingOrbit 3 (2 * n)) :
    (∃ S, symmetricOrbitInclusion n S = O) ↔
      ∃ T : Tiling 3 (2 * n), HasSymmetry T ∧ Quotient.mk _ T = O := by
  constructor
  · rintro ⟨S, h⟩
    induction S using Quotient.inductionOn with
    | h T => exact ⟨T.val, T.property, h⟩
  · rintro ⟨T, hT, h⟩
    exact ⟨Quotient.mk _ ⟨T, hT⟩, h⟩

noncomputable def symmetricFixedEquiv (n : ℕ) (g : RectangleSymmetry) (hg : g ≠ 1) :
    MulAction.fixedBy (SymmetricTilings n) g ≃ MulAction.fixedBy (Tiling 3 (2 * n)) g where
  toFun T := ⟨T.val.val, congrArg Subtype.val T.property⟩
  invFun T := ⟨⟨T.val, ⟨g, hg, T.property⟩⟩, Subtype.ext T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem twice_symmetric_orbit_count (n : ℕ) :
    2 * symmetricOrbitCount n = fixedCount 3 n vertical + fixedCount 3 n halfTurn := by
  classical
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group RectangleSymmetry (SymmetricTilings n)
  have hi : Fintype.card (MulAction.fixedBy (SymmetricTilings n) (1 : RectangleSymmetry)) = symmetricCount n := by
    simp [MulAction.fixedBy, symmetricCount]
  have hg (g : RectangleSymmetry) (hg : g ≠ 1) :
      Fintype.card (MulAction.fixedBy (SymmetricTilings n) g) = fixedCount 3 n g :=
    Fintype.card_congr (symmetricFixedEquiv n g hg)
  have ho : Fintype.card (Quotient (MulAction.orbitRel RectangleSymmetry (SymmetricTilings n))) =
      symmetricOrbitCount n := Fintype.card_congr (Equiv.refl _)
  rw [sum_rectangle_symmetries, hi, hg horizontal (by decide), hg vertical (by decide),
    hg halfTurn (by decide), horizontal_fixed_card_three, symmetry_card_four, ho] at h
  have hs := symmetric_count_add_one n
  omega

noncomputable def tilingProbability (n : ℕ) : ℝ := (symmetricCount n : ℝ) / ordinaryCount 3 n
noncomputable def orbitProbability (n : ℕ) : ℝ := (symmetricOrbitCount n : ℝ) / a n

theorem orbit_positive (n : ℕ) : 0 < a n := by have h := four_mul_a n; omega

theorem tiling_probability_formula (n : ℕ) :
    tilingProbability n = ((fixedCount 3 n vertical : ℝ) + fixedCount 3 n halfTurn - 1) / ordinaryCount 3 n := by
  have h : (symmetricCount n : ℝ) + 1 = (fixedCount 3 n vertical : ℝ) + fixedCount 3 n halfTurn := by
    exact_mod_cast symmetric_count_add_one n
  unfold tilingProbability
  congr 1
  linarith

theorem orbit_probability_formula (n : ℕ) :
    orbitProbability n = ((fixedCount 3 n vertical : ℝ) + fixedCount 3 n halfTurn) / (2 * a n) := by
  have h : 2 * (symmetricOrbitCount n : ℝ) = (fixedCount 3 n vertical : ℝ) + fixedCount 3 n halfTurn := by
    exact_mod_cast twice_symmetric_orbit_count n
  rw [← h, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rfl

theorem probabilities_mem_unit_interval (n : ℕ) :
    0 ≤ tilingProbability n ∧ tilingProbability n ≤ 1 ∧
    0 ≤ orbitProbability n ∧ orbitProbability n ≤ 1 := by
  have hd : (0 : ℝ) < ordinaryCount 3 n := by exact_mod_cast ordinary_positive n
  have ha : (0 : ℝ) < a n := by exact_mod_cast orbit_positive n
  have hs : (symmetricCount n : ℝ) ≤ ordinaryCount 3 n := by
    exact_mod_cast (Nat.le.intro (symmetric_count_complement n))
  have ho : (symmetricOrbitCount n : ℝ) ≤ a n := by
    exact_mod_cast Fintype.card_le_of_injective _ (symmetricOrbitInclusion_injective n)
  exact ⟨div_nonneg (Nat.cast_nonneg _) hd.le, (div_le_one hd).2 hs,
    div_nonneg (Nat.cast_nonneg _) ha.le, (div_le_one ha).2 ho⟩

theorem probabilities_zero : tilingProbability 0 = 1 ∧ orbitProbability 0 = 1 := by
  simp [tiling_probability_formula, orbit_probability_formula]

end Domino.Asymptotic
