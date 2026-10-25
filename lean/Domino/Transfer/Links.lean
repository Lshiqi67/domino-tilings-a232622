module

public import Domino.Transfer.Grid
public import Domino.Transfer.ThreeRows

/-! 切口行集合与列内竖砖确定的相邻配对关系；局部度数与单列规则等价。 -/

@[expose] public section

namespace Domino

def GridLink (H : ℕ → State 3) (V : ℕ → Finset (Fin 2)) (a b : GridCell) : Prop :=
  (a.1 = b.1 ∧ b.2 + 1 = a.2 ∧ a.1 ∈ H a.2) ∨
  (a.1 = b.1 ∧ b.2 = a.2 + 1 ∧ a.1 ∈ H (a.2 + 1)) ∨
  (a.2 = b.2 ∧ ((a.1 = 0 ∧ b.1 = 1) ∨ (a.1 = 1 ∧ b.1 = 0)) ∧ 0 ∈ V a.2) ∨
  (a.2 = b.2 ∧ ((a.1 = 1 ∧ b.1 = 2) ∨ (a.1 = 2 ∧ b.1 = 1)) ∧ 1 ∈ V a.2)

theorem gridLink_symmetric (H : ℕ → State 3) (V : ℕ → Finset (Fin 2))
    (a b : GridCell) (h : GridLink H V a b) : GridLink H V b a := by
  rcases h with ⟨hr, hc, hm⟩ | ⟨hr, hc, hm⟩ | ⟨hc, hr, hm⟩ | ⟨hc, hr, hm⟩
  · exact Or.inr (Or.inl ⟨hr.symm, hc.symm, by simpa [← hr, hc] using hm⟩)
  · exact Or.inl ⟨hr.symm, hc.symm, by simpa [← hr, hc] using hm⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hc.symm, by tauto, by simpa [← hc] using hm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hc.symm, by tauto, by simpa [← hc] using hm⟩))

theorem gridLink_adjacent (H : ℕ → State 3) (V : ℕ → Finset (Fin 2))
    (a b : GridCell) (h : GridLink H V a b) : GridAdjacent a b := by
  rcases h with ⟨hr, hc, _⟩ | ⟨hr, hc, _⟩ | ⟨hc, hr, _⟩ | ⟨hc, hr, _⟩
  · exact Or.inl ⟨hr, Or.inr hc⟩
  · exact Or.inl ⟨hr, Or.inl hc.symm⟩
  · apply Or.inr
    rcases hr with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [hc, ha, hb]
  · apply Or.inr
    rcases hr with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [hc, ha, hb]

theorem nat_predecessor_iff (i j : ℕ) : j + 1 = i ↔ j = i - 1 ∧ 0 < i := by omega

theorem gridLink_row_zero (H : ℕ → State 3) (V : ℕ → Finset (Fin 2))
    (i : ℕ) (b : GridCell) :
    GridLink H V (0, i) b ↔
      (b = (0, i - 1) ∧ (0 < i ∧ 0 ∈ H i)) ∨
      (b = (0, i + 1) ∧ 0 ∈ H (i + 1)) ∨
      (b = (1, i) ∧ 0 ∈ V i) := by
  rcases b with ⟨r, j⟩
  have hp : i = j + 1 ↔ j = i - 1 ∧ 0 < i := by omega
  fin_cases r <;> simp [GridLink, Prod.mk.injEq, eq_comm]
  simp only [hp]
  tauto

theorem gridLink_row_one (H : ℕ → State 3) (V : ℕ → Finset (Fin 2))
    (i : ℕ) (b : GridCell) :
    GridLink H V (1, i) b ↔
      (b = (1, i - 1) ∧ (0 < i ∧ 1 ∈ H i)) ∨
      (b = (1, i + 1) ∧ 1 ∈ H (i + 1)) ∨
      (b = (0, i) ∧ 0 ∈ V i) ∨ (b = (2, i) ∧ 1 ∈ V i) := by
  rcases b with ⟨r, j⟩
  have hp : i = j + 1 ↔ j = i - 1 ∧ 0 < i := by omega
  fin_cases r <;> simp [GridLink, Prod.mk.injEq, eq_comm]
  simp only [hp]
  tauto

theorem gridLink_row_two (H : ℕ → State 3) (V : ℕ → Finset (Fin 2))
    (i : ℕ) (b : GridCell) :
    GridLink H V (2, i) b ↔
      (b = (2, i - 1) ∧ (0 < i ∧ 2 ∈ H i)) ∨
      (b = (2, i + 1) ∧ 2 ∈ H (i + 1)) ∨
      (b = (1, i) ∧ 1 ∈ V i) := by
  rcases b with ⟨r, j⟩
  have hp : i = j + 1 ↔ j = i - 1 ∧ 0 < i := by omega
  fin_cases r <;> simp [GridLink, Prod.mk.injEq, eq_comm]
  simp only [hp]
  tauto

theorem unique_three_iff {α : Type*} (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (P Q R : Prop)
    [Decidable P] [Decidable Q] [Decidable R] :
    (∃! x, (x = a ∧ P) ∨ (x = b ∧ Q) ∨ (x = c ∧ R)) ↔
      (if P then 1 else 0) + (if Q then 1 else 0) + (if R then 1 else 0) = (1 : ℕ) := by
  by_cases hp : P <;> by_cases hq : Q <;> by_cases hr : R <;>
    simp_all [ExistsUnique] <;> aesop

theorem unique_four_iff {α : Type*} (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (P Q R S : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable S] :
    (∃! x, (x = a ∧ P) ∨ (x = b ∧ Q) ∨ (x = c ∧ R) ∨ (x = d ∧ S)) ↔
      (if P then 1 else 0) + (if Q then 1 else 0) + (if R then 1 else 0) +
        (if S then 1 else 0) = (1 : ℕ) := by
  by_cases hp : P <;> by_cases hq : Q <;> by_cases hr : R <;> by_cases hs : S <;>
    simp_all [ExistsUnique] <;> aesop

theorem columnRule_iff_unique_neighbors (H : ℕ → State 3) (V : ℕ → Finset (Fin 2))
    (h0 : H 0 = ∅) (i : ℕ) :
    ColumnRule (H i) (H (i + 1)) (V i) ↔ ∀ r : Fin 3, ∃! b, GridLink H V (r, i) b := by
  have hin (r : Fin 3) : (0 < i ∧ r ∈ H i) ↔ r ∈ H i := by
    by_cases hi : i = 0
    · simp [hi, h0]
    · simp [Nat.pos_of_ne_zero hi]
  have hne (r : Fin 3) : (r, i - 1) ≠ (r, i + 1) := by
    intro h
    have := congrArg Prod.snd h
    omega
  have hrow (r : Fin 3) :
      (∃! b, GridLink H V (r, i) b) ↔
      ((if r ∈ H i then 1 else 0) + (if r ∈ H (i + 1) then 1 else 0) +
      (if (r = 0 ∨ r = 1) ∧ 0 ∈ V i then 1 else 0) +
      (if (r = 1 ∨ r = 2) ∧ 1 ∈ V i then 1 else 0) = (1 : ℕ)) := by
    have hz := (existsUnique_congr (gridLink_row_zero H V i)).trans
      (unique_three_iff (0, i - 1) (0, i + 1) (1, i) (hne 0) (by simp) (by simp)
        (0 < i ∧ 0 ∈ H i) (0 ∈ H (i + 1)) (0 ∈ V i))
    have ho := (existsUnique_congr (gridLink_row_one H V i)).trans
      (unique_four_iff (1, i - 1) (1, i + 1) (0, i) (2, i)
        (hne 1) (by simp) (by simp) (by simp) (by simp) (by simp)
        (0 < i ∧ 1 ∈ H i) (1 ∈ H (i + 1)) (0 ∈ V i) (1 ∈ V i))
    have ht := (existsUnique_congr (gridLink_row_two H V i)).trans
      (unique_three_iff (2, i - 1) (2, i + 1) (1, i) (hne 2) (by simp) (by simp)
        (0 < i ∧ 2 ∈ H i) (2 ∈ H (i + 1)) (1 ∈ V i))
    fin_cases r
    · simpa [hin] using hz
    · simpa [hin] using ho
    · simpa [hin] using ht
  exact forall_congr' fun r => (hrow r).symm

@[simp] theorem gridLink_horizontal (H : ℕ → State 3) (V : ℕ → Finset (Fin 2))
    (r : Fin 3) (i : ℕ) : GridLink H V (r, i) (r, i + 1) ↔ r ∈ H (i + 1) := by
  have h1 : i + 1 + 1 ≠ i := by omega
  simp [GridLink, h1]

@[simp] theorem gridLink_vertical_zero (H : ℕ → State 3) (V : ℕ → Finset (Fin 2))
    (i : ℕ) : GridLink H V (0, i) (1, i) ↔ 0 ∈ V i := by simp [GridLink]

@[simp] theorem gridLink_vertical_one (H : ℕ → State 3) (V : ℕ → Finset (Fin 2))
    (i : ℕ) : GridLink H V (1, i) (2, i) ↔ 1 ∈ V i := by simp [GridLink]

end Domino
