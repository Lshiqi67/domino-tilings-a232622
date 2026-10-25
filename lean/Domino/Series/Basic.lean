module

public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic

/-! M6 的系数级数、移位与奇偶插零工具；没有收敛性假设。 -/

@[expose] public section

namespace Domino

open PowerSeries

noncomputable def countSeries (f : ℕ → ℕ) : PowerSeries ℚ := mk fun n => (f n : ℚ)

@[simp] theorem coeff_countSeries (f : ℕ → ℕ) (n : ℕ) :
    coeff n (countSeries f) = (f n : ℚ) := coeff_mk _ _

theorem coeff_X_mul_at (F : PowerSeries ℚ) (n : ℕ) :
    coeff n (X * F) = if 1 ≤ n then coeff (n - 1) F else 0 := by
  simpa only [pow_one] using coeff_X_pow_mul' F 1 n

theorem series_second_order (f : ℕ → ℚ)
    (h : ∀ n, f (n + 2) + f n = 4 * f (n + 1)) :
    (1 - 4 * X + X ^ 2) * mk f = C (f 0) + C (f 1 - 4 * f 0) * X := by
  ext n
  rcases n with _ | _ | n
  · simp [add_mul, sub_mul, mul_assoc]
  · simp [add_mul, sub_mul, mul_assoc, coeff_succ_X_mul, coeff_X_pow_mul']
  · have hn0 : n + 2 ≠ 0 := by omega
    have hn1 : n + 2 ≠ 1 := by omega
    change coeff (n + 2) _ = coeff (n + 2) _
    simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub,
      coeff_ofNat_mul, coeff_X_mul_at, coeff_X_pow_mul', coeff_mk,
      coeff_C_mul, coeff_C, coeff_X]
    simp only [show 1 ≤ n + 2 by omega, show 2 ≤ n + 2 by omega, ite_true,
      hn0, hn1, ite_false, mul_zero]
    rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
    linarith [h n]

theorem series_shift (f : ℕ → ℚ) :
    X * mk (fun n => f (n + 1)) = mk f - C (f 0) := by
  simpa using (sub_const_eq_X_mul_shift (mk f)).symm

noncomputable def doubleSeries : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ :=
  expand 2 (by decide)

@[simp] theorem coeff_doubleSeries_even (F : PowerSeries ℚ) (j : ℕ) :
    coeff (2 * j) (doubleSeries F) = coeff j F := by
  exact coeff_expand_mul 2 (by decide) F j

@[simp] theorem coeff_doubleSeries_odd (F : PowerSeries ℚ) (j : ℕ) :
    coeff (2 * j + 1) (doubleSeries F) = 0 := by
  apply coeff_expand_of_not_dvd 2 (by decide)
  omega

@[simp] theorem coeff_X_doubleSeries_even (F : PowerSeries ℚ) (j : ℕ) :
    coeff (2 * j) (X * doubleSeries F) = 0 := by
  cases j with
  | zero => simp
  | succ j =>
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, coeff_succ_X_mul]
      exact coeff_doubleSeries_odd F j

@[simp] theorem coeff_X_doubleSeries_odd (F : PowerSeries ℚ) (j : ℕ) :
    coeff (2 * j + 1) (X * doubleSeries F) = coeff j F := by
  rw [coeff_succ_X_mul, coeff_doubleSeries_even]

theorem series_ext_parity (F G : PowerSeries ℚ)
    (he : ∀ j, coeff (2 * j) F = coeff (2 * j) G)
    (ho : ∀ j, coeff (2 * j + 1) F = coeff (2 * j + 1) G) : F = G := by
  ext n
  have hn : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1 := by omega
  rcases hn with hn | hn
  · rw [hn]; exact he _
  · rw [hn]; exact ho _

end Domino
