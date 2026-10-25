module

public import Domino.Transfer.Count

/-! B05：由真实逐列递推归纳全部宽度的支持与二维计数。 -/

@[expose] public section

namespace Domino

theorem state_three_cases : ∀ S : State 3,
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨ S = {0, 2} ∨
      S = {1, 2} ∨ S = Finset.univ := by decide

theorem sum_states_three (f : State 3 → ℕ) :
    ∑ S : State 3, f S = f ∅ + f {0} + f {1} + f {2} + f {0, 1} + f {0, 2} +
      f {1, 2} + f Finset.univ := by
  have hu : (Finset.univ : Finset (State 3)) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, Finset.univ} := by decide
  rw [hu]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  omega

def evenProfile (a b : ℕ) (S : State 3) : ℕ :=
  if S = ∅ then a else if S = {0, 1} ∨ S = {1, 2} then b else 0

def oddProfile (a b : ℕ) (S : State 3) : ℕ :=
  if S = {0} ∨ S = {2} then a + b else if S = Finset.univ then a else 0

theorem even_profile_step (a b : ℕ) (q : State 3) :
    ∑ p : State 3, evenProfile a b p * transfer3 p q = oddProfile a b q := by
  rw [sum_states_three]
  rcases state_three_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [evenProfile, oddProfile, transfer3, ite_eq_left, ite_eq_right,
      mul_zero, mul_one, add_zero]

theorem odd_profile_step (a b : ℕ) (q : State 3) :
    ∑ p : State 3, oddProfile a b p * transfer3 p q = evenProfile (3 * a + 2 * b) (a + b) q := by
  rw [sum_states_three]
  rcases state_three_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [evenProfile, oddProfile, transfer3, ite_eq_left, ite_eq_right,
      mul_zero, mul_one, zero_add, add_zero]
  omega

def profilePair : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | j + 1 => (3 * (profilePair j).1 + 2 * (profilePair j).2,
               (profilePair j).1 + (profilePair j).2)

def alpha (j : ℕ) : ℕ := (profilePair j).1
def beta (j : ℕ) : ℕ := (profilePair j).2

@[simp] theorem alpha_zero : alpha 0 = 1 := rfl
@[simp] theorem beta_zero : beta 0 = 0 := rfl
theorem alpha_succ (j : ℕ) : alpha (j + 1) = 3 * alpha j + 2 * beta j := rfl
theorem beta_succ (j : ℕ) : beta (j + 1) = alpha j + beta j := rfl

theorem profile_even_odd (j : ℕ) :
    (∀ S, profileCount (2 * j) S = evenProfile (alpha j) (beta j) S) ∧
    (∀ S, profileCount (2 * j + 1) S = oddProfile (alpha j) (beta j) S) := by
  have odd_of_even (k : ℕ)
      (h : ∀ S, profileCount (2 * k) S = evenProfile (alpha k) (beta k) S) :
      ∀ S, profileCount (2 * k + 1) S = oddProfile (alpha k) (beta k) S := by
    intro S
    rw [profile_count_succ]
    simp only [h]
    exact even_profile_step _ _ S
  induction j with
  | zero =>
      have he (S : State 3) : profileCount 0 S = evenProfile (alpha 0) (beta 0) S := by
        simp [profile_count_zero, evenProfile]
      exact ⟨he, odd_of_even 0 he⟩
  | succ j ih =>
      have he (S : State 3) : profileCount (2 * (j + 1)) S = evenProfile (alpha (j + 1)) (beta (j + 1)) S := by
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, profile_count_succ]
        simp only [ih.2, alpha_succ, beta_succ]
        exact odd_profile_step _ _ S
      exact ⟨he, odd_of_even (j + 1) he⟩

theorem profile_even (j : ℕ) (S : State 3) :
    profileCount (2 * j) S = evenProfile (alpha j) (beta j) S := (profile_even_odd j).1 S

theorem profile_odd (j : ℕ) (S : State 3) :
    profileCount (2 * j + 1) S = oddProfile (alpha j) (beta j) S := (profile_even_odd j).2 S

theorem profile_even_support (j : ℕ) (S : State 3) (h : profileCount (2 * j) S ≠ 0) :
    S = ∅ ∨ S = {0, 1} ∨ S = {1, 2} := by
  rw [profile_even] at h
  by_contra hn
  simp [evenProfile, not_or.mp hn |>.1, not_or.mp hn |>.2] at h

theorem profile_odd_support (j : ℕ) (S : State 3) (h : profileCount (2 * j + 1) S ≠ 0) :
    S = {0} ∨ S = {2} ∨ S = Finset.univ := by
  rw [profile_odd] at h
  by_contra hn
  have hs : ¬(S = {0} ∨ S = {2}) := by tauto
  have hu : S ≠ Finset.univ := by tauto
  simp [oddProfile, hs, hu] at h

end Domino
