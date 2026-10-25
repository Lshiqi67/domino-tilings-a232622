module

public import Domino.ThreeRows.Ordinary
public import Domino.HalfBoard.Horizontal

/-! B07：对真实终端计数求和，得到所有半宽的固定点奇偶公式。 -/

@[expose] public section

namespace Domino

theorem sum_symmetric_terminals (f : State 3 → ℕ) :
    ∑ S : SymmetricTerminal, f S.val = f ∅ + f {1} + f {0, 2} + f Finset.univ := by
  have hs : ∀ S : State 3, S ∈ ({∅, {1}, {0, 2}, Finset.univ} : Finset (State 3)) ↔
      reverseState S = S := by decide
  rw [← Finset.sum_subtype _ hs f]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  omega

theorem reflection_even_profile (j : ℕ) : fixedCount 3 (2 * j) vertical = alpha j + 2 * beta j := by
  rw [reflection_fixed_count]
  simp only [profile_even, sum_states_three]
  simp (disch := decide) only [evenProfile, ite_eq_left, ite_eq_right]
  omega

theorem reflection_odd_profile (j : ℕ) : fixedCount 3 (2 * j + 1) vertical = 3 * alpha j + 2 * beta j := by
  rw [reflection_fixed_count]
  simp only [profile_odd, sum_states_three]
  simp (disch := decide) only [oddProfile, ite_eq_left, ite_eq_right]
  omega

theorem halfTurn_even_profile (j : ℕ) : fixedCount 3 (2 * j) halfTurn = alpha j := by
  rw [halfTurn_fixed_count]
  simp only [profile_even, sum_symmetric_terminals]
  simp (disch := decide) only [evenProfile, ite_eq_left, ite_eq_right, add_zero]

theorem halfTurn_odd_profile (j : ℕ) : fixedCount 3 (2 * j + 1) halfTurn = alpha j := by
  rw [halfTurn_fixed_count]
  simp only [profile_odd, sum_symmetric_terminals]
  simp (disch := decide) only [oddProfile, ite_eq_left, ite_eq_right, zero_add]

theorem reflection_even_add (j : ℕ) :
    fixedCount 3 (2 * j) vertical + 2 * ordinaryCount 3 j = ordinaryCount 3 (j + 1) := by
  rw [reflection_even_profile, ordinary_eq_alpha, ordinary_eq_alpha, alpha_succ]
  omega

theorem reflection_even_bound (j : ℕ) : 2 * ordinaryCount 3 j ≤ ordinaryCount 3 (j + 1) := by
  have h := reflection_even_add j
  omega

theorem reflection_even (j : ℕ) :
    fixedCount 3 (2 * j) vertical = ordinaryCount 3 (j + 1) - 2 * ordinaryCount 3 j := by
  have h := reflection_even_add j
  omega

theorem reflection_odd (j : ℕ) : fixedCount 3 (2 * j + 1) vertical = ordinaryCount 3 (j + 1) := by
  rw [reflection_odd_profile, ordinary_eq_alpha, alpha_succ]

theorem halfTurn_even (j : ℕ) : fixedCount 3 (2 * j) halfTurn = ordinaryCount 3 j := by
  rw [halfTurn_even_profile, ordinary_eq_alpha]

theorem halfTurn_odd (j : ℕ) : fixedCount 3 (2 * j + 1) halfTurn = ordinaryCount 3 j := by
  rw [halfTurn_odd_profile, ordinary_eq_alpha]

theorem fixed_counts_parity (j : ℕ) :
    fixedCount 3 (2 * j) vertical = ordinaryCount 3 (j + 1) - 2 * ordinaryCount 3 j ∧
    fixedCount 3 (2 * j + 1) vertical = ordinaryCount 3 (j + 1) ∧
    fixedCount 3 (2 * j) halfTurn = ordinaryCount 3 j ∧
    fixedCount 3 (2 * j + 1) halfTurn = ordinaryCount 3 j :=
  ⟨reflection_even j, reflection_odd j, halfTurn_even j, halfTurn_odd j⟩

end Domino
