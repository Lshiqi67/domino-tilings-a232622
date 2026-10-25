module

public import Domino.FiveRows.Encoding
public import Domino.FiveRows.SeriesTools

/-! 五行上下反射固定点所需的真实两行铺法计数。 -/

@[expose] public section

namespace Domino.FiveRows

open PowerSeries

def twoLift : Matrix (Fin 4) (Fin 2) ℕ := ![![1, 0], ![0, 0], ![0, 0], ![0, 1]]

def twoMatrix : Matrix (Fin 2) (Fin 2) ℕ := ![![2, 1], ![1, 1]]

def twoInitial : Fin 2 → ℕ := ![1, 0]

def twoCompressed : ℕ → Fin 2 → ℕ
  | 0 => twoInitial
  | n + 1 => twoMatrix.mulVec (twoCompressed n)

theorem two_transfer_lift : encodedTransfer 2 * encodedTransfer 2 * twoLift =
    twoLift * twoMatrix := by decide

theorem two_profile (n : ℕ) : profile 2 (2 * n) = twoLift.mulVec (twoCompressed n) := by
  induction n with
  | zero =>
    funext p
    rw [profile, General.profile_count_zero]
    exact (show ∀ p : Fin 4, (if maskState 2 p = ∅ then 1 else 0) =
      twoLift.mulVec twoInitial p by decide) p
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      profile_succ 2 maskState_two_bijective, profile_succ 2 maskState_two_bijective,
      ih, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      two_transfer_lift, ← Matrix.mulVec_mulVec]
    rfl

theorem two_ordinary (n : ℕ) : ordinaryCount 2 n = twoCompressed n 0 := by
  rw [General.ordinary_count_profile]
  change profile 2 (2 * n) 0 = _
  rw [two_profile]
  simp [twoLift, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def denominatorH {R : Type*} [Ring R] (t : R) : R := 1 - 3 * t + t ^ 2

theorem two_certificate_identity {R : Type*} [CommRing R] (t : R) :
    (1 - t • twoMatrix.map (fun a => (a : R))).mulVec ![1 - t, t] =
      denominatorH t • (fun i => (twoInitial i : R)) := by
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, twoMatrix,
      Matrix.map, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      denominatorH, twoInitial] <;> ring

theorem two_series_identity :
    denominatorH (X : PowerSeries ℚ) * countSeries (ordinaryCount 2) = 1 - X := by
  have hc : (General.seriesPencil (rationalMatrix twoMatrix)).mulVec ![1 - X, X] =
      denominatorH (X : PowerSeries ℚ) • (fun i => C (twoCompressed 0 i : ℚ)) := by
    simpa [General.seriesPencil, rationalMatrix, Matrix.map_map, Function.comp_def,
      twoCompressed] using (two_certificate_identity (X : PowerSeries ℚ))
  have h := congrFun (vector_series_certificate twoMatrix twoCompressed (fun _ => rfl)
    (denominatorH X) ![1 - X, X] hc) 0
  simpa only [Pi.smul_apply, smul_eq_mul, vectorSeries, ← two_ordinary,
    Matrix.cons_val_zero] using h

end Domino.FiveRows
