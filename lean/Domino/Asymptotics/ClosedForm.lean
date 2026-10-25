module

public import Domino.ThreeRows.Ordinary
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! 三行真实普通铺法的实数闭式、正性和主增长项。 -/

@[expose] public section

namespace Domino.Asymptotic

open Filter Topology

noncomputable def growth : ℝ := 2 + Real.sqrt 3
noncomputable def decay : ℝ := 2 - Real.sqrt 3
noncomputable def leading : ℝ := (3 + Real.sqrt 3) / 6
noncomputable def trailing : ℝ := (3 - Real.sqrt 3) / 6
noncomputable def d (n : ℕ) : ℝ := ordinaryCount 3 n

theorem sqrt_three_bounds : 1 < Real.sqrt 3 ∧ Real.sqrt 3 < 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

theorem growth_gt_one : 1 < growth := by unfold growth; linarith [sqrt_three_bounds.1]
theorem growth_pos : 0 < growth := lt_trans zero_lt_one growth_gt_one
theorem growth_ne_zero : growth ≠ 0 := ne_of_gt growth_pos
theorem decay_bounds : 0 < decay ∧ decay < 1 := by
  unfold decay
  constructor <;> linarith [sqrt_three_bounds.1, sqrt_three_bounds.2]

theorem growth_mul_decay : growth * decay = 1 := by
  unfold growth decay
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem decay_eq_inv : decay = growth⁻¹ := by
  apply (mul_left_cancel₀ growth_ne_zero)
  rw [growth_mul_decay, mul_inv_cancel₀ growth_ne_zero]

theorem characteristic_roots : growth ^ 2 + 1 = 4 * growth ∧ decay ^ 2 + 1 = 4 * decay := by
  unfold growth decay
  constructor <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem leading_pos : 0 < leading := by unfold leading; positivity
theorem trailing_pos : 0 < trailing := by unfold trailing; linarith [sqrt_three_bounds.2]
theorem coefficients_sum : leading + trailing = 1 := by unfold leading trailing; ring

theorem ordinary_closed_form (n : ℕ) : d n = leading * growth ^ n + trailing * decay ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [d, coefficients_sum]
  | one =>
    rw [d, ordinary_initial_values.2]
    norm_num [leading, trailing, growth, decay]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  | more n ih0 ih1 =>
    have h : d (n + 2) + d n = 4 * d (n + 1) := by
      dsimp only [d]
      exact_mod_cast ordinary_recurrence_add n
    rw [ih0, ih1] at h
    simp only [pow_succ]
    linear_combination h - (leading * growth ^ n) * characteristic_roots.1 -
      (trailing * decay ^ n) * characteristic_roots.2

theorem d_pos (n : ℕ) : 0 < d n := by
  dsimp only [d]
  exact_mod_cast ordinary_positive n
theorem d_ne_zero (n : ℕ) : d n ≠ 0 := ne_of_gt (d_pos n)

theorem ordinary_normalized (n : ℕ) :
    d n / growth ^ n = leading + trailing * (decay / growth) ^ n := by
  rw [ordinary_closed_form, div_pow]
  field_simp [growth_ne_zero]

theorem decay_pow_tendsto : Tendsto (fun n : ℕ => decay ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one decay_bounds.1.le decay_bounds.2

theorem inverse_growth_tendsto : Tendsto (fun n : ℕ => (growth ^ n)⁻¹) atTop (𝓝 0) := by
  simpa only [decay_eq_inv, inv_pow] using decay_pow_tendsto

theorem ordinary_normalized_tendsto :
    Tendsto (fun n : ℕ => d n / growth ^ n) atTop (𝓝 leading) := by
  have hq : 0 ≤ decay / growth := div_nonneg decay_bounds.1.le growth_pos.le
  have hq1 : decay / growth < 1 := (div_lt_one growth_pos).2 (lt_trans decay_bounds.2 growth_gt_one)
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => leading) atTop (𝓝 leading)).add
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).const_mul trailing)
  simpa only [← ordinary_normalized, mul_zero, add_zero] using h

theorem ordinary_asymptotic_ratio :
    Tendsto (fun n : ℕ => d n / (leading * growth ^ n)) atTop (𝓝 1) := by
  have h := ordinary_normalized_tendsto.div_const leading
  simpa only [div_mul_eq_div_div_swap, div_self (ne_of_gt leading_pos)] using h

end Domino.Asymptotic
