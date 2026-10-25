module

public import Domino.OddHeight.Column

/-! 列配对在行反转下的传递，以及局部矩阵的对称性。 -/

@[expose] public section

namespace Domino.General

variable {m : ℕ}

def reverseRowBonds (V : RowBonds m) : RowBonds m :=
  V.map (Equiv.prodCongr Fin.revPerm Fin.revPerm).toEmbedding

@[simp] theorem mem_reverseRowBonds (V : RowBonds m) (r s : Fin m) :
    (r, s) ∈ reverseRowBonds V ↔ (r.rev, s.rev) ∈ V := Finset.mem_map_equiv

theorem rowAdjacent_reverse (r s : Fin m) : RowAdjacent r.rev s.rev ↔ RowAdjacent r s := by
  simp only [RowAdjacent, Fin.val_rev]
  have hr := r.isLt
  have hs := s.isLt
  omega

theorem reverseState_union (p q : State m) : reverseState (p ∪ q) = reverseState p ∪ reverseState q := by
  ext r
  simp

theorem rowValid_reverse (H : State m) (V : RowBonds m) (h : RowValid H V) :
    RowValid (reverseState H) (reverseRowBonds V) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s hrs
    exact (rowAdjacent_reverse r s).mp (h.1 _ _ ((mem_reverseRowBonds V r s).mp hrs))
  · intro r s hrs
    exact (mem_reverseRowBonds V s r).mpr (h.2.1 _ _ ((mem_reverseRowBonds V r s).mp hrs))
  · intro r
    simp only [mem_reverseRowBonds, mem_reverseState]
    constructor
    · rintro ⟨s, hs⟩
      exact (h.2.2.1 r.rev).mp ⟨s.rev, hs⟩
    · intro hr
      obtain ⟨s, hs⟩ := (h.2.2.1 r.rev).mpr hr
      exact ⟨s.rev, by simpa using hs⟩
  · intro r s t hrs hrt
    have he := h.2.2.2 r.rev s.rev t.rev
      ((mem_reverseRowBonds V r s).mp hrs) ((mem_reverseRowBonds V r t).mp hrt)
    exact Fin.rev_injective he

theorem legal_reverse (p q : State m) : Legal p q ↔ Legal (reverseState p) (reverseState q) := by
  have forward (p q : State m) (h : Legal p q) : Legal (reverseState p) (reverseState q) := by
    refine ⟨Finset.disjoint_left.mpr ?_, ?_⟩
    · intro r hp hq
      exact Finset.disjoint_left.mp h.1 ((mem_reverseState p r).mp hp) ((mem_reverseState q r).mp hq)
    · obtain ⟨⟨V, hV⟩⟩ := h.2
      exact ⟨⟨reverseRowBonds V, by simpa only [reverseState_union] using rowValid_reverse _ _ hV⟩⟩
  exact ⟨forward p q, fun h => by simpa only [reverseState_twice] using forward _ _ h⟩

end Domino.General
