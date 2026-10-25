module

public import Domino.ThreeRows.FixedCounts
public import Domino.Symmetry.Burnside

/-! M5：实际轨道基数的自然数恒等式、整除性与有理数奇偶公式。 -/

@[expose] public section

namespace Domino

theorem four_mul_a (n : ℕ) :
    4 * a n = ordinaryCount 3 n + 1 + fixedCount 3 n vertical + fixedCount 3 n halfTurn := by
  simpa only [a, horizontal_fixed_card_three] using four_mul_orbitCount 3 n

theorem orbit_even_add (j : ℕ) :
    4 * a (2 * j) + ordinaryCount 3 j = ordinaryCount 3 (2 * j) + 1 + ordinaryCount 3 (j + 1) := by
  have hb := four_mul_a (2 * j)
  have hv := reflection_even_add j
  rw [halfTurn_even] at hb
  omega

theorem orbit_odd_mul (j : ℕ) :
    4 * a (2 * j + 1) = ordinaryCount 3 (2 * j + 1) + 1 +
      ordinaryCount 3 (j + 1) + ordinaryCount 3 j := by
  rw [four_mul_a, reflection_odd, halfTurn_odd]

theorem orbit_even_numerator_bound (j : ℕ) :
    ordinaryCount 3 j ≤ ordinaryCount 3 (2 * j) + 1 + ordinaryCount 3 (j + 1) := by
  have h := orbit_even_add j
  omega

theorem orbit_even_numerator (j : ℕ) :
    ordinaryCount 3 (2 * j) + 1 + ordinaryCount 3 (j + 1) - ordinaryCount 3 j = 4 * a (2 * j) := by
  have h := orbit_even_add j
  omega

theorem orbit_even_divisible (j : ℕ) :
    4 ∣ ordinaryCount 3 (2 * j) + 1 + ordinaryCount 3 (j + 1) - ordinaryCount 3 j :=
  ⟨a (2 * j), orbit_even_numerator j⟩

theorem orbit_odd_divisible (j : ℕ) :
    4 ∣ ordinaryCount 3 (2 * j + 1) + 1 + ordinaryCount 3 (j + 1) + ordinaryCount 3 j :=
  ⟨a (2 * j + 1), (orbit_odd_mul j).symm⟩

theorem orbit_even (j : ℕ) :
    a (2 * j) = (ordinaryCount 3 (2 * j) + 1 + ordinaryCount 3 (j + 1) - ordinaryCount 3 j) / 4 := by
  rw [orbit_even_numerator]
  omega

theorem orbit_odd (j : ℕ) :
    a (2 * j + 1) = (ordinaryCount 3 (2 * j + 1) + 1 + ordinaryCount 3 (j + 1) + ordinaryCount 3 j) / 4 := by
  rw [← orbit_odd_mul]
  omega

theorem orbit_even_rat (j : ℕ) :
    (a (2 * j) : ℚ) = ((ordinaryCount 3 (2 * j) : ℚ) + 1 + ordinaryCount 3 (j + 1) - ordinaryCount 3 j) / 4 := by
  have h : 4 * (a (2 * j) : ℚ) + ordinaryCount 3 j =
      (ordinaryCount 3 (2 * j) : ℚ) + 1 + ordinaryCount 3 (j + 1) := by exact_mod_cast orbit_even_add j
  linarith

theorem orbit_odd_rat (j : ℕ) :
    (a (2 * j + 1) : ℚ) = ((ordinaryCount 3 (2 * j + 1) : ℚ) + 1 +
      ordinaryCount 3 (j + 1) + ordinaryCount 3 j) / 4 := by
  have h : 4 * (a (2 * j + 1) : ℚ) = (ordinaryCount 3 (2 * j + 1) : ℚ) + 1 +
      ordinaryCount 3 (j + 1) + ordinaryCount 3 j := by exact_mod_cast orbit_odd_mul j
  linarith

end Domino
