module

public import Domino.OddHeight.HalfTurn
public import Domino.OddHeight.OddReflection
public import Domino.Symmetry.Burnside

@[expose] public section

namespace Domino.General

theorem odd_height_four_counts (k n : ℕ) :
    4 * orbitCount (2 * k + 1) n =
      (transferMatrix (m := 2 * k + 1) ^ (2 * n)) ∅ ∅ +
      (transferMatrix (m := k) ^ (2 * n)) ∅ ∅ +
      (∑ S : State (2 * k + 1), (transferMatrix ^ n) ∅ S) +
      (∑ S : SymmetricTerminal (2 * k + 1), (transferMatrix ^ n) ∅ S.val) := by
  classical
  rw [four_mul_orbitCount, horizontal_fixed_count_odd, reflection_fixed_count, halfTurn_fixed_count]
  simp only [ordinary_count_profile, profile_count_matrix]

theorem odd_height_divisible (k n : ℕ) :
    4 ∣ (transferMatrix (m := 2 * k + 1) ^ (2 * n)) ∅ ∅ +
      (transferMatrix (m := k) ^ (2 * n)) ∅ ∅ +
      (∑ S : State (2 * k + 1), (transferMatrix ^ n) ∅ S) +
      (∑ S : SymmetricTerminal (2 * k + 1), (transferMatrix ^ n) ∅ S.val) :=
  ⟨orbitCount (2 * k + 1) n, (odd_height_four_counts k n).symm⟩

theorem zero_height_transfer : transferMatrix (m := 0) = 1 := by
  classical
  have he : Legal (∅ : State 0) ∅ := legal_empty_even 0
  ext p q
  have hp : p = ∅ := Subsingleton.elim _ _
  have hq : q = ∅ := Subsingleton.elim _ _
  subst p; subst q
  simp [transferMatrix, transfer, he]

theorem odd_height_empty (k : ℕ) : orbitCount (2 * k + 1) 0 = 1 := orbitCount_zero _

theorem horizontal_top_inverse (k n : ℕ)
    (T : {T : Tiling (2 * k + 1) (2 * n) // horizontal • T = T}) :
    (horizontalFixedEquivTop k n).symm (horizontalFixedEquivTop k n T) = T :=
  (horizontalFixedEquivTop k n).symm_apply_apply T

theorem top_horizontal_inverse (k n : ℕ) (T : Tiling k (2 * n)) :
    horizontalFixedEquivTop k n ((horizontalFixedEquivTop k n).symm T) = T :=
  (horizontalFixedEquivTop k n).apply_symm_apply T

end Domino.General
