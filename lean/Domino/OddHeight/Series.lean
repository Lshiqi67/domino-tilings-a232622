module

public import Domino.OddHeight.OrbitCounts
public import Domino.OddHeight.RationalSeries
public import Domino.OddHeight.EvenRuns

/-! 任意正奇数高度的实际铺法轨道生成函数、有理性及最终常系数递推。 -/

@[expose] public section

namespace Domino.General

open PowerSeries

noncomputable def rationalTransfer (m : ℕ) : Matrix (State m) (State m) ℚ :=
  (Nat.castRingHom ℚ).mapMatrix transferMatrix

theorem rationalTransfer_pow (m n : ℕ) (p q : State m) :
    (rationalTransfer m ^ n) p q = ((transferMatrix ^ n) p q : ℚ) := by
  have h := (Nat.castRingHom ℚ).mapMatrix.map_pow (transferMatrix (m := m)) n
  exact (congrArg (fun A : Matrix (State m) (State m) ℚ => A p q) h).symm

noncomputable def orbitSeries (k : ℕ) : PowerSeries ℚ := countSeries (orbitCount (2 * k + 1))

theorem orbit_matrix_series (k : ℕ) :
    orbitSeries k = C (1 / 4 : ℚ) *
      (matrixSeries (rationalTransfer (2 * k + 1) ^ 2) ∅ ∅ +
       matrixSeries (rationalTransfer k ^ 2) ∅ ∅ +
       (∑ S : State (2 * k + 1), matrixSeries (rationalTransfer (2 * k + 1)) ∅ S) +
       (∑ S : SymmetricTerminal (2 * k + 1), matrixSeries (rationalTransfer (2 * k + 1)) ∅ S.val)) := by
  classical
  apply PowerSeries.ext
  intro n
  simp only [orbitSeries, coeff_countSeries, coeff_C_mul, map_add, map_sum,
    matrixSeries, coeff_mk, ← pow_mul, rationalTransfer_pow]
  have h : (4 : ℚ) * orbitCount (2 * k + 1) n =
      ((transferMatrix (m := 2 * k + 1) ^ (2 * n)) ∅ ∅ : ℚ) +
      ((transferMatrix (m := k) ^ (2 * n)) ∅ ∅ : ℚ) +
      (∑ S : State (2 * k + 1), ((transferMatrix ^ n) ∅ S : ℚ)) +
      (∑ S : SymmetricTerminal (2 * k + 1), ((transferMatrix ^ n) ∅ S.val : ℚ)) := by
    exact_mod_cast odd_height_four_counts k n
  linarith

theorem odd_height_orbit_rational (k : ℕ) : RationalSeries (orbitSeries k) := by
  classical
  rw [orbit_matrix_series]
  apply rational_scale
  apply rational_add
  · apply rational_add
    · exact rational_add (matrix_entry_rational _ _ _) (matrix_entry_rational _ _ _)
    · exact rational_sum _ _ (fun _ _ => matrix_entry_rational _ _ _)
  · exact rational_sum _ _ (fun _ _ => matrix_entry_rational _ _ _)

theorem odd_height_eventual_recurrence (k : ℕ) :
    ∃ (d N : ℕ) (c : ℕ → ℚ), c 0 ≠ 0 ∧
      ∀ n, N ≤ n → (orbitCount (2 * k + 1) (n + d) : ℚ) =
        -(c 0)⁻¹ * ∑ i ∈ Finset.range d,
          c (i + 1) * (orbitCount (2 * k + 1) (n + d - (i + 1)) : ℚ) := by
  simpa only [orbitSeries, coeff_countSeries] using
    rational_eventual_recurrence (odd_height_orbit_rational k)

theorem odd_height_rational_witness (k : ℕ) :
    ∃ P Q : Polynomial ℚ, Q.coeff 0 ≠ 0 ∧
      (Q : PowerSeries ℚ) * countSeries (orbitCount (2 * k + 1)) = P :=
  odd_height_orbit_rational k

end Domino.General
