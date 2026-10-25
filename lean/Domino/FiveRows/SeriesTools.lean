module

public import Domino.OddHeight.MatrixSeries

/-! 从自然数向量递推到形式幂级数，再由有限证书得到全部系数。 -/

@[expose] public section

namespace Domino.FiveRows

open PowerSeries

variable {d : ℕ}

noncomputable def vectorSeries (u : ℕ → Fin d → ℕ) (i : Fin d) : PowerSeries ℚ :=
  countSeries fun n => u n i

def rationalMatrix (M : Matrix (Fin d) (Fin d) ℕ) : Matrix (Fin d) (Fin d) ℚ :=
  (Nat.castRingHom ℚ).mapMatrix M

theorem vector_series_recurrence (M : Matrix (Fin d) (Fin d) ℕ) (u : ℕ → Fin d → ℕ)
    (hu : ∀ n, u (n + 1) = M.mulVec (u n)) :
    (General.seriesPencil (rationalMatrix M)).mulVec (vectorSeries u) =
      fun i => C (u 0 i : ℚ) := by
  unfold General.seriesPencil
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  funext i
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [vectorSeries, countSeries]
  | succ n =>
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, coeff_succ_X_mul,
      Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, coeff_C_mul, vectorSeries,
      coeff_countSeries, coeff_C, Nat.succ_ne_zero, ite_false]
    simp [hu, Matrix.mulVec, dotProduct, rationalMatrix, Nat.cast_sum, Nat.cast_mul]

theorem vector_series_certificate (M : Matrix (Fin d) (Fin d) ℕ) (u : ℕ → Fin d → ℕ)
    (hu : ∀ n, u (n + 1) = M.mulVec (u n)) (P : PowerSeries ℚ) (N : Fin d → PowerSeries ℚ)
    (hc : (General.seriesPencil (rationalMatrix M)).mulVec N = P • (fun i => C (u 0 i : ℚ))) :
    P • vectorSeries u = N := by
  have h : (General.seriesPencil (rationalMatrix M)).mulVec (P • vectorSeries u) =
      (General.seriesPencil (rationalMatrix M)).mulVec N := by
    rw [Matrix.mulVec_smul, vector_series_recurrence M u hu, hc]
  have hh := congrArg ((General.matrixSeries (rationalMatrix M)).mulVec) h
  simpa only [Matrix.mulVec_mulVec, General.matrix_geometric_right, Matrix.one_mulVec] using hh

theorem count_series_dot (w : Fin d → ℕ) (u : ℕ → Fin d → ℕ) :
    countSeries (fun n => w ⬝ᵥ u n) = ∑ i, C (w i : ℚ) * vectorSeries u i := by
  apply PowerSeries.ext
  intro n
  simp [vectorSeries, dotProduct, Nat.cast_sum, Nat.cast_mul]

end Domino.FiveRows
