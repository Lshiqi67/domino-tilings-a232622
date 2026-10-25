module

public import Domino.FiveRows.Certificate
public import Domino.FiveRows.TwoRows

/-! 真实五行铺法及三个非恒等对称的固定点级数。 -/

@[expose] public section

namespace Domino.FiveRows

open PowerSeries

noncomputable def ordinarySeries : PowerSeries ℚ := countSeries (ordinaryCount 5)
noncomputable def horizontalSeries : PowerSeries ℚ := countSeries fun n => fixedCount 5 n horizontal
noncomputable def verticalSeries : PowerSeries ℚ := countSeries fun n => fixedCount 5 n vertical
noncomputable def halfTurnSeries : PowerSeries ℚ := countSeries fun n => fixedCount 5 n halfTurn

def numeratorV {R : Type*} [Ring R] (t : R) : R :=
  1 + 8 * t + 8 * t ^ 2 - 23 * t ^ 3 - 9 * t ^ 4 + 16 * t ^ 5 - t ^ 7

def numeratorR {R : Type*} [Ring R] (t : R) : R :=
  1 + 2 * t - 6 * t ^ 2 - 7 * t ^ 3 + 7 * t ^ 4 + 6 * t ^ 5 - 2 * t ^ 6 - t ^ 7

theorem ordinary_series_identity :
    denominatorP (X : PowerSeries ℚ) * ordinarySeries = 1 - 7 * X + 7 * X ^ 2 - X ^ 3 := by
  rw [ordinarySeries, show ordinaryCount 5 = (fun n => compressed n 0) from funext ordinary_compressed]
  simpa [vectorSeries, numeratorColumn] using compressed_series_identity 0

theorem horizontal_series_identity :
    denominatorH (X : PowerSeries ℚ) * horizontalSeries = 1 - X := by
  have h : horizontalSeries = countSeries (ordinaryCount 2) := by
    apply PowerSeries.ext
    intro n
    simp only [horizontalSeries, coeff_countSeries]
    rw [General.horizontal_fixed_count_odd 2]
  rw [h]
  exact two_series_identity

theorem count_series_parity (f : ℕ → ℕ) (e o : ℕ → ℕ)
    (he : ∀ n, f (2 * n) = e n) (ho : ∀ n, f (2 * n + 1) = o n) :
    countSeries f = doubleSeries (countSeries e) + X * doubleSeries (countSeries o) := by
  apply series_ext_parity <;> intro n <;> simp [he, ho]

theorem doubled_weighted_series (w : Fin 6 → ℕ) :
    denominatorP ((X : PowerSeries ℚ) ^ 2) *
        doubleSeries (countSeries (fun n => w ⬝ᵥ compressed n)) =
      ∑ i, C (w i : ℚ) * numeratorColumn (X ^ 2) i := by
  have h := congrArg doubleSeries (weighted_series_identity w)
  simpa [denominatorP, numeratorColumn, doubleSeries, Fin.sum_univ_succ, map_ofNat] using h

theorem vertical_series_identity :
    denominatorP ((X : PowerSeries ℚ) ^ 2) * verticalSeries = numeratorV X := by
  rw [verticalSeries, count_series_parity _ _ _
    (fun n => (fixed_counts_compressed n).1) (fun n => (fixed_counts_compressed n).2.1)]
  rw [mul_add, mul_left_comm _ X, doubled_weighted_series, doubled_weighted_series]
  norm_num [weightVE, weightVO, numeratorColumn, Fin.sum_univ_succ, numeratorV]
  ring

theorem halfTurn_series_identity :
    denominatorP ((X : PowerSeries ℚ) ^ 2) * halfTurnSeries = numeratorR X := by
  rw [halfTurnSeries, count_series_parity _ _ _
    (fun n => (fixed_counts_compressed n).2.2.1) (fun n => (fixed_counts_compressed n).2.2.2)]
  rw [mul_add, mul_left_comm _ X, doubled_weighted_series, doubled_weighted_series]
  norm_num [weightRE, weightRO, numeratorColumn, Fin.sum_univ_succ, numeratorR]
  ring

theorem fixed_series_identities :
    denominatorH (X : PowerSeries ℚ) * horizontalSeries = 1 - X ∧
    denominatorP (X ^ 2) * verticalSeries = numeratorV X ∧
    denominatorP (X ^ 2) * halfTurnSeries = numeratorR X :=
  ⟨horizontal_series_identity, vertical_series_identity, halfTurn_series_identity⟩

end Domino.FiveRows
