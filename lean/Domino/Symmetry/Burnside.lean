module

public import Domino.Symmetry.Counting
public import Mathlib.Tactic

/-! C02：实际四元群作用的 Burnside 恒等式；不需要作用忠实。 -/

@[expose] public section

namespace Domino

theorem sum_rectangle_symmetries (f : RectangleSymmetry → ℕ) :
    ∑ g, f g = f 1 + f horizontal + f vertical + f halfTurn := by
  have hu : (Finset.univ : Finset RectangleSymmetry) = {1, horizontal, vertical, halfTurn} := by decide
  rw [hu]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  omega

theorem fixedCount_one (m n : ℕ) : fixedCount m n 1 = ordinaryCount m n := by
  classical
  simp [fixedCount, ordinaryCount]

theorem four_mul_orbitCount (m n : ℕ) :
    4 * orbitCount m n = ordinaryCount m n + fixedCount m n horizontal +
      fixedCount m n vertical + fixedCount m n halfTurn := by
  classical
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group RectangleSymmetry (Tiling m (2 * n))
  have hf (g : RectangleSymmetry) : Fintype.card (MulAction.fixedBy (Tiling m (2 * n)) g) = fixedCount m n g :=
    Fintype.card_congr (Equiv.refl _)
  have ho : Fintype.card (Quotient (MulAction.orbitRel RectangleSymmetry (Tiling m (2 * n)))) = orbitCount m n :=
    Fintype.card_congr (Equiv.refl _)
  simp only [hf, ho, sum_rectangle_symmetries, fixedCount_one, symmetry_card_four] at h
  omega

theorem fixed_sum_divisible_four (m n : ℕ) :
    4 ∣ ordinaryCount m n + fixedCount m n horizontal + fixedCount m n vertical + fixedCount m n halfTurn :=
  ⟨orbitCount m n, (four_mul_orbitCount m n).symm⟩

theorem orbitCount_eq_average (m n : ℕ) :
    orbitCount m n = (ordinaryCount m n + fixedCount m n horizontal +
      fixedCount m n vertical + fixedCount m n halfTurn) / 4 := by
  have h := four_mul_orbitCount m n
  omega

theorem orbitCount_average_rat (m n : ℕ) :
    (orbitCount m n : ℚ) = ((ordinaryCount m n : ℚ) + fixedCount m n horizontal +
      fixedCount m n vertical + fixedCount m n halfTurn) / 4 := by
  have h : 4 * (orbitCount m n : ℚ) = (ordinaryCount m n : ℚ) + fixedCount m n horizontal +
      fixedCount m n vertical + fixedCount m n halfTurn := by exact_mod_cast four_mul_orbitCount m n
  linarith

end Domino
