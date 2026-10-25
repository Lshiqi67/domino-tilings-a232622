module

public import Domino.OddHeight.Column

/-! 偶数行的一列有唯一的相邻配对，含高度零。 -/

@[expose] public section

namespace Domino.General

def evenPartner {n : ℕ} (r : Fin (2 * n)) : Fin (2 * n) :=
  if h : r.val % 2 = 0 then ⟨r.val + 1, by have := r.isLt; omega⟩
  else ⟨r.val - 1, by have := r.isLt; omega⟩

theorem evenPartner_adjacent {n : ℕ} (r : Fin (2 * n)) : RowAdjacent r (evenPartner r) := by
  dsimp [evenPartner, RowAdjacent]
  split_ifs with h
  · exact Or.inl rfl
  · right
    change r.val - 1 + 1 = r.val
    omega

theorem evenPartner_twice {n : ℕ} (r : Fin (2 * n)) : evenPartner (evenPartner r) = r := by
  apply Fin.ext
  by_cases h : r.val % 2 = 0
  · have ho : (r.val + 1) % 2 ≠ 0 := by omega
    simp [evenPartner, h, ho]
  · have he : (r.val - 1) % 2 = 0 := by omega
    simp only [evenPartner, h, ↓reduceDIte, he]
    omega

def evenRowBonds (n : ℕ) : RowBonds (2 * n) :=
  Finset.univ.filter fun rs => rs.2 = evenPartner rs.1

theorem evenRowBonds_valid (n : ℕ) : RowValid ∅ (evenRowBonds n) := by
  have mem (r s : Fin (2 * n)) : (r, s) ∈ evenRowBonds n ↔ s = evenPartner r := by
    simp [evenRowBonds]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s hs
    rw [mem] at hs
    rw [hs]
    exact evenPartner_adjacent r
  · intro r s hs
    rw [mem] at hs ⊢
    rw [hs, evenPartner_twice]
  · intro r
    exact ⟨fun _ => Finset.notMem_empty _, fun _ => ⟨evenPartner r, (mem _ _).mpr rfl⟩⟩
  · intro r s t hs ht
    exact ((mem r s).mp hs).trans ((mem r t).mp ht).symm

theorem legal_empty_even (n : ℕ) : Legal (∅ : State (2 * n)) ∅ :=
  ⟨Finset.disjoint_empty_left _, ⟨⟨evenRowBonds n, by simpa using evenRowBonds_valid n⟩⟩⟩

end Domino.General
