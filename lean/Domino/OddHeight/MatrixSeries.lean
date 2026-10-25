module

public import Domino.Series.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! 有限矩阵的形式几何级数，以及由行列式给出的非零常数项分母。 -/

@[expose] public section

namespace Domino.General

open PowerSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def matrixSeries (M : Matrix ι ι ℚ) : Matrix ι ι (PowerSeries ℚ) :=
  fun i j => mk fun n => (M ^ n) i j

noncomputable def matrixPencil (M : Matrix ι ι ℚ) : Matrix ι ι (Polynomial ℚ) :=
  1 - (Polynomial.X : Polynomial ℚ) • M.map Polynomial.C

noncomputable def seriesPencil (M : Matrix ι ι ℚ) : Matrix ι ι (PowerSeries ℚ) :=
  1 - (X : PowerSeries ℚ) • M.map C

theorem matrix_geometric_left (M : Matrix ι ι ℚ) : seriesPencil M * matrixSeries M = 1 := by
  unfold seriesPencil
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [matrixSeries, Matrix.one_apply]
  | succ n =>
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, coeff_succ_X_mul,
      Matrix.mul_apply, map_sum, coeff_C_mul, Matrix.map_apply, matrixSeries, coeff_mk]
    by_cases h : i = j <;> simp [pow_succ', Matrix.mul_apply, Matrix.one_apply, h]

theorem matrix_geometric_right (M : Matrix ι ι ℚ) : matrixSeries M * seriesPencil M = 1 := by
  unfold seriesPencil
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [matrixSeries, Matrix.one_apply]
  | succ n =>
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, coeff_succ_X_mul,
      Matrix.mul_apply, map_sum, coeff_mul_C, Matrix.map_apply, matrixSeries, coeff_mk]
    by_cases h : i = j <;> simp [pow_succ, Matrix.mul_apply, Matrix.one_apply, h]

omit [Fintype ι] in
theorem matrixPencil_coe (M : Matrix ι ι ℚ) :
    (matrixPencil M).map (fun p => (p : PowerSeries ℚ)) = seriesPencil M := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> simp [matrixPencil, seriesPencil, h]
  all_goals exact mul_comm _ _

omit [Fintype ι] in
theorem matrixPencil_eval_zero (M : Matrix ι ι ℚ) :
    (matrixPencil M).map (Polynomial.eval 0) = 1 := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> simp [matrixPencil, Matrix.one_apply, h]

theorem matrix_denominator_constant (M : Matrix ι ι ℚ) : (matrixPencil M).det.coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  change (Polynomial.evalRingHom 0) (matrixPencil M).det = 1
  rw [RingHom.map_det]
  change ((matrixPencil M).map (Polynomial.evalRingHom 0)).det = 1
  rw [show (matrixPencil M).map (Polynomial.evalRingHom 0) = 1 from matrixPencil_eval_zero M]
  exact Matrix.det_one

theorem matrix_entry_denominator (M : Matrix ι ι ℚ) (i j : ι) :
    ((matrixPencil M).det : PowerSeries ℚ) * matrixSeries M i j =
      ((matrixPencil M).adjugate i j : PowerSeries ℚ) := by
  have h := congrArg (fun A : Matrix ι ι (PowerSeries ℚ) =>
    (seriesPencil M).adjugate * A) (matrix_geometric_left M)
  rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one] at h
  have he := congrArg (fun A : Matrix ι ι (PowerSeries ℚ) => A i j) h
  change (seriesPencil M).det * matrixSeries M i j = (seriesPencil M).adjugate i j at he
  rw [← matrixPencil_coe] at he
  change ((Polynomial.coeToPowerSeries.ringHom (R := ℚ)).mapMatrix (matrixPencil M)).det *
    matrixSeries M i j =
    ((Polynomial.coeToPowerSeries.ringHom (R := ℚ)).mapMatrix (matrixPencil M)).adjugate i j at he
  rw [← RingHom.map_det (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) (matrixPencil M),
    ← RingHom.map_adjugate (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) (matrixPencil M)] at he
  exact he

def RationalSeries (F : PowerSeries ℚ) : Prop :=
  ∃ P Q : Polynomial ℚ, Q.coeff 0 ≠ 0 ∧ (Q : PowerSeries ℚ) * F = P

theorem matrix_entry_rational (M : Matrix ι ι ℚ) (i j : ι) : RationalSeries (matrixSeries M i j) :=
  ⟨(matrixPencil M).adjugate i j, (matrixPencil M).det,
    by rw [matrix_denominator_constant]; norm_num, matrix_entry_denominator M i j⟩

theorem matrix_geometric_constant (M : Matrix ι ι ℚ) :
    (matrixSeries M).map (coeff 0) = 1 := by
  apply Matrix.ext
  intro i j
  simp [matrixSeries]

theorem matrix_geometric_unique (M : Matrix ι ι ℚ) (U : Matrix ι ι (PowerSeries ℚ))
    (hU : seriesPencil M * U = 1) : U = matrixSeries M := by
  calc
    U = (matrixSeries M * seriesPencil M) * U := by rw [matrix_geometric_right, Matrix.one_mul]
    _ = matrixSeries M := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]

end Domino.General
