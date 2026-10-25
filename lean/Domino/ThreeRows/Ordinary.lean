module

public import Domino.ThreeRows.ProfileRecurrence

/-! B06：二维辅助数列连接实际完整铺法，再得到二阶递推。 -/

@[expose] public section

namespace Domino

theorem ordinary_eq_alpha (j : ℕ) : ordinaryCount 3 j = alpha j := by
  rw [ordinary_count_profile, profile_even]
  simp [evenProfile]

theorem alpha_eq_profile (j : ℕ) : alpha j = profileCount (2 * j) ∅ := by
  simp [profile_even, evenProfile]

theorem beta_eq_profile (j : ℕ) : beta j = profileCount (2 * j) {0, 1} := by
  simp [profile_even, evenProfile]

theorem alpha_recurrence_add (j : ℕ) : alpha (j + 2) + alpha j = 4 * alpha (j + 1) := by
  rw [show j + 2 = (j + 1) + 1 by omega, alpha_succ (j + 1), beta_succ, alpha_succ]
  omega

theorem ordinary_recurrence_add (j : ℕ) :
    ordinaryCount 3 (j + 2) + ordinaryCount 3 j = 4 * ordinaryCount 3 (j + 1) := by
  simp only [ordinary_eq_alpha, alpha_recurrence_add]

theorem ordinary_recurrence_bound (j : ℕ) : ordinaryCount 3 j ≤ 4 * ordinaryCount 3 (j + 1) := by
  have h := ordinary_recurrence_add j
  omega

theorem ordinary_recurrence (j : ℕ) :
    ordinaryCount 3 (j + 2) = 4 * ordinaryCount 3 (j + 1) - ordinaryCount 3 j := by
  have h := ordinary_recurrence_add j
  omega

theorem ordinary_recurrence_int (j : ℕ) :
    (ordinaryCount 3 (j + 2) : ℤ) = 4 * (ordinaryCount 3 (j + 1) : ℤ) - ordinaryCount 3 j := by
  have h := ordinary_recurrence_add j
  omega

theorem ordinary_initial_values : ordinaryCount 3 0 = 1 ∧ ordinaryCount 3 1 = 3 := by
  simp [ordinary_eq_alpha, alpha, profilePair]

theorem ordinary_monotone_step (j : ℕ) : ordinaryCount 3 j ≤ ordinaryCount 3 (j + 1) := by
  rw [ordinary_eq_alpha, ordinary_eq_alpha, alpha_succ]
  omega

theorem ordinary_positive (j : ℕ) : 0 < ordinaryCount 3 j := by
  induction j with
  | zero => simp
  | succ j ih => exact lt_of_lt_of_le ih (ordinary_monotone_step j)

def profileMatrix : Matrix (Fin 2) (Fin 2) ℕ := !![3, 2; 1, 1]

theorem profile_matrix_recurrence (j : ℕ) :
    ![alpha (j + 1), beta (j + 1)] = profileMatrix.mulVec ![alpha j, beta j] := by
  ext i
  fin_cases i <;> simp [profileMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, alpha_succ, beta_succ]

theorem profile_matrix_characteristic :
    profileMatrix ^ 2 + 1 = 4 • profileMatrix := by
  ext i k
  fin_cases i <;> fin_cases k <;> decide

end Domino
