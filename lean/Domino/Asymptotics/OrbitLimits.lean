module

public import Domino.Asymptotics.ParityLimits

/-! Burnside 主项与均匀轨道抽样概率的极限。 -/

@[expose] public section

namespace Domino.Asymptotic

open Filter Topology

theorem inverse_ordinary_tendsto : Tendsto (fun n : ℕ => (d n)⁻¹) atTop (𝓝 0) := by
  have h := inverse_growth_tendsto.div ordinary_normalized_tendsto (ne_of_gt leading_pos)
  simp only [zero_div] at h
  convert h using 1
  ext n
  change (d n)⁻¹ = (growth ^ n)⁻¹ / (d n / growth ^ n)
  field_simp [growth_ne_zero, d_ne_zero]

theorem orbit_div_ordinary (n : ℕ) :
    (a n : ℝ) / d n = (1 + tilingProbability n + 2 / d n) / 4 := by
  have hb : 4 * (a n : ℝ) = d n + 1 + fixedCount 3 n vertical + fixedCount 3 n halfTurn := by
    dsimp only [d]; exact_mod_cast four_mul_a n
  rw [tiling_probability_formula]
  change (a n : ℝ) / d n = (1 + ((_ : ℝ) + _ - 1) / d n + 2 / d n) / 4
  field_simp [d_ne_zero]
  linarith

theorem orbit_div_ordinary_tendsto :
    Tendsto (fun n : ℕ => (a n : ℝ) / d n) atTop (𝓝 (1 / 4)) := by
  have h := ((tiling_probability_tendsto_zero.const_add 1).add
    (inverse_ordinary_tendsto.const_mul 2)).div_const 4
  simp only [mul_zero, add_zero] at h
  convert h using 1
  ext n
  simpa only [div_eq_mul_inv] using orbit_div_ordinary n

theorem orbit_normalized_tendsto :
    Tendsto (fun n : ℕ => (a n : ℝ) / growth ^ n) atTop (𝓝 (leading / 4)) := by
  have h := orbit_div_ordinary_tendsto.mul ordinary_normalized_tendsto
  simpa [div_mul_div_cancel₀, d_ne_zero, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using h

theorem orbit_asymptotic_ratio :
    Tendsto (fun n : ℕ => (a n : ℝ) / ((leading / 4) * growth ^ n)) atTop (𝓝 1) := by
  have h := orbit_normalized_tendsto.div_const (leading / 4)
  simpa only [div_mul_eq_div_div_swap, div_self (div_ne_zero (ne_of_gt leading_pos) (by norm_num) : leading / 4 ≠ 0)] using h

theorem orbit_probability_normalized (n : ℕ) :
    orbitProbability n = (tilingProbability n + (d n)⁻¹) / (2 * ((a n : ℝ) / d n)) := by
  have ha : (a n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast orbit_positive n)
  rw [orbit_probability_formula, tiling_probability_formula]
  change ((_ : ℝ) + _) / (2 * a n) = (((_ : ℝ) + _ - 1) / d n + (d n)⁻¹) / (2 * ((a n : ℝ) / d n))
  field_simp [d_ne_zero, ha]
  ring

theorem orbit_probability_tendsto_zero : Tendsto orbitProbability atTop (𝓝 0) := by
  have h := (tiling_probability_tendsto_zero.add inverse_ordinary_tendsto).div
    (orbit_div_ordinary_tendsto.const_mul 2) (by norm_num : (2 : ℝ) * (1 / 4) ≠ 0)
  simp only [add_zero, zero_div] at h
  convert h using 1
  ext n
  exact orbit_probability_normalized n

end Domino.Asymptotic
