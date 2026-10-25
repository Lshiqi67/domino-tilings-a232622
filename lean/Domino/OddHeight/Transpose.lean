module

public import Domino.Symmetry.PathAction

/-! 交换行列的几何铺法等价；将上下反射变为左右反射。 -/

@[expose] public section

namespace Domino.General

def transposeBonds {m w : ℕ} (R : Bonds m w) : Bonds w m :=
  R.map (Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _)).toEmbedding

@[simp] theorem mem_transposeBonds {m w : ℕ} (R : Bonds m w) (a b : Cell w m) :
    (a, b) ∈ transposeBonds R ↔ ((a.2, a.1), (b.2, b.1)) ∈ R := Finset.mem_map_equiv

theorem transpose_bonds_valid {m w : ℕ} (R : BondCover m w ∅) :
    BondValid ∅ (transposeBonds R.val) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h := R.property.1 _ _ ((mem_transposeBonds R.val a b).mp hab)
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
  · intro a b hab
    exact (mem_transposeBonds R.val b a).mpr (R.property.2.1 _ _ ((mem_transposeBonds R.val a b).mp hab))
  · intro a
    constructor
    · intro _; exact Finset.notMem_empty _
    · intro _
      obtain ⟨b, hb⟩ := (R.property.2.2.1 (a.2, a.1)).mpr (Finset.notMem_empty _)
      exact ⟨(b.2, b.1), (mem_transposeBonds R.val _ _).mpr hb⟩
  · intro a b c hab hac
    have h := R.property.2.2.2 _ _ _ ((mem_transposeBonds R.val a b).mp hab)
      ((mem_transposeBonds R.val a c).mp hac)
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

noncomputable def transposeTiling {m w : ℕ} (T : Tiling m w) : Tiling w m :=
  (coverEquivBonds w m ∅).symm ⟨transposeBonds (coverBonds T),
    transpose_bonds_valid ((coverEquivBonds m w ∅) T)⟩

theorem transposeTiling_bonds {m w : ℕ} (T : Tiling m w) :
    coverBonds (transposeTiling T) = transposeBonds (coverBonds T) :=
  congrArg Subtype.val ((coverEquivBonds w m ∅).apply_symm_apply _)

theorem transposeTiling_twice {m w : ℕ} (T : Tiling m w) :
    transposeTiling (transposeTiling T) = T := by
  apply (coverEquivBonds m w ∅).injective
  apply Subtype.ext
  change coverBonds (transposeTiling (transposeTiling T)) = coverBonds T
  rw [transposeTiling_bonds, transposeTiling_bonds]
  ext ab
  rcases ab with ⟨a, b⟩
  simp

noncomputable def transposeTilingEquiv (m w : ℕ) : Tiling m w ≃ Tiling w m where
  toFun := transposeTiling
  invFun := transposeTiling
  left_inv := transposeTiling_twice
  right_inv := transposeTiling_twice

theorem transposeTiling_horizontal {m w : ℕ} (T : Tiling m w) :
    transposeTiling (horizontal • T) = vertical • transposeTiling T := by
  apply (coverEquivBonds w m ∅).injective
  apply Subtype.ext
  change coverBonds (transposeTiling (horizontal • T)) = coverBonds (vertical • transposeTiling T)
  ext ab
  rcases ab with ⟨a, b⟩
  rw [transposeTiling_bonds, mem_transposeBonds, coverBonds_action, coverBonds_action,
    transposeTiling_bonds, mem_transposeBonds]
  rfl

noncomputable def horizontalFixedTransposeEquiv (m w : ℕ) :
    {T : Tiling m w // horizontal • T = T} ≃ {T : Tiling w m // vertical • T = T} :=
  (transposeTilingEquiv m w).subtypeEquiv fun T => by
    change horizontal • T = T ↔ vertical • transposeTiling T = transposeTiling T
    rw [← transposeTiling_horizontal]
    exact (transposeTilingEquiv m w).injective.eq_iff.symm

end Domino.General
