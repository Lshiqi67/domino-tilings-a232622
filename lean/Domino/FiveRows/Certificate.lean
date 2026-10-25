module

public import Domino.FiveRows.Counts
public import Domino.FiveRows.SeriesTools

/-! 多项式向量证书及其对全部自然数指标的含义。 -/

@[expose] public section

namespace Domino.FiveRows

open PowerSeries

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def denominatorP {R : Type*} [Ring R] (t : R) : R :=
  1 - 15 * t + 32 * t ^ 2 - 15 * t ^ 3 + t ^ 4

def numeratorColumn {R : Type*} [Ring R] (t : R) : Fin 6 → R :=
  ![1 - 7 * t + 7 * t ^ 2 - t ^ 3,
    3 * t - 4 * t ^ 2 + t ^ 3,
    2 * t - 5 * t ^ 2 + t ^ 3,
    t + t ^ 2, t - t ^ 3, t - t ^ 3]

theorem certificate_identity {R : Type*} [CommRing R] (t : R) :
    (1 - t • matrixM.map (fun a => (a : R))).mulVec (numeratorColumn t) =
      denominatorP t • (fun i => (initial i : R)) := by
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, matrixM,
      Matrix.map, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      numeratorColumn, denominatorP, initial] <;> ring

theorem polynomial_certificate :
    (1 - (Polynomial.X : Polynomial ℚ) • matrixM.map (fun a => (a : Polynomial ℚ))).mulVec
        (numeratorColumn (Polynomial.X : Polynomial ℚ)) =
      denominatorP (Polynomial.X : Polynomial ℚ) • (fun i => (initial i : Polynomial ℚ)) :=
  certificate_identity (Polynomial.X : Polynomial ℚ)

theorem compressed_series_identity (i : Fin 6) :
    denominatorP (X : PowerSeries ℚ) * vectorSeries compressed i = numeratorColumn X i := by
  have hc : (General.seriesPencil (rationalMatrix matrixM)).mulVec (numeratorColumn X) =
      denominatorP (X : PowerSeries ℚ) • (fun i => C (compressed 0 i : ℚ)) := by
    simpa [General.seriesPencil, rationalMatrix, Matrix.map_map, Function.comp_def,
      compressed] using (certificate_identity (X : PowerSeries ℚ))
  exact congrFun (vector_series_certificate matrixM compressed (fun _ => rfl)
    (denominatorP X) (numeratorColumn X) hc) i

theorem weighted_series_identity (w : Fin 6 → ℕ) :
    denominatorP (X : PowerSeries ℚ) * countSeries (fun n => w ⬝ᵥ compressed n) =
      ∑ i, C (w i : ℚ) * numeratorColumn X i := by
  rw [count_series_dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, mul_comm (denominatorP X), mul_assoc, compressed_series_identity]

end Domino.FiveRows
