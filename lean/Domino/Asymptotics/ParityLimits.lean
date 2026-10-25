module

public import Domino.Asymptotics.ClosedForm
public import Domino.Asymptotics.Sampling

/-! 奇偶子列的精确归一化恒等式及首项渐近常数。 -/

@[expose] public section

namespace Domino.Asymptotic

open Filter Topology

theorem affine_index_tendsto (k b : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => k * n + b) atTop atTop := by
  apply tendsto_atTop.2
  intro a
  filter_upwards [eventually_ge_atTop a] with n hn
  nlinarith

theorem eventually_of_even_odd {P : ℕ → Prop}
    (he : ∀ᶠ j in atTop, P (2 * j)) (ho : ∀ᶠ j in atTop, P (2 * j + 1)) :
    ∀ᶠ n in atTop, P n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  obtain ⟨M, hM⟩ := eventually_atTop.1 ho
  filter_upwards [eventually_ge_atTop (2 * (N + M) + 1)] with n hn
  have hp : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1 := by omega
  rcases hp with hp | hp
  · rw [hp]; exact hN _ (by omega)
  · rw [hp]; exact hM _ (by omega)

theorem tendsto_of_even_odd {f : ℕ → ℝ} {c : ℝ}
    (he : Tendsto (fun j => f (2 * j)) atTop (𝓝 c))
    (ho : Tendsto (fun j => f (2 * j + 1)) atTop (𝓝 c)) : Tendsto f atTop (𝓝 c) := by
  apply Filter.tendsto_def.2
  intro s hs
  exact eventually_of_even_odd (he.eventually hs) (ho.eventually hs)

theorem tiling_probability_even (j : ℕ) :
    tilingProbability (2 * j) = (d (j + 1) - d j - 1) / d (2 * j) := by
  have h : (fixedCount 3 (2 * j) vertical : ℝ) + 2 * d j = d (j + 1) := by
    dsimp only [d]; exact_mod_cast reflection_even_add j
  rw [tiling_probability_formula, halfTurn_even]
  change ((_ : ℝ) + d j - 1) / d (2 * j) = _
  congr 1
  linarith

theorem tiling_probability_odd (j : ℕ) :
    tilingProbability (2 * j + 1) = (d (j + 1) + d j - 1) / d (2 * j + 1) := by
  rw [tiling_probability_formula, reflection_odd, halfTurn_odd]
  rfl

theorem probability_even_scaled (j : ℕ) :
    tilingProbability (2 * j) * growth ^ j =
      (growth * (d (j + 1) / growth ^ (j + 1)) - d j / growth ^ j - (growth ^ j)⁻¹) /
        (d (2 * j) / growth ^ (2 * j)) := by
  rw [tiling_probability_even]
  field_simp [growth_ne_zero, d_ne_zero, pow_add, pow_mul]
  ring

theorem probability_odd_scaled (j : ℕ) :
    tilingProbability (2 * j + 1) * growth ^ j =
      (growth * (d (j + 1) / growth ^ (j + 1)) + d j / growth ^ j - (growth ^ j)⁻¹) /
        (growth * (d (2 * j + 1) / growth ^ (2 * j + 1))) := by
  rw [tiling_probability_odd]
  field_simp [growth_ne_zero, d_ne_zero, pow_add, pow_mul]
  ring

theorem ordinary_normalized_affine (k b : ℕ) (hk : 0 < k) :
    Tendsto (fun j => d (k * j + b) / growth ^ (k * j + b)) atTop (𝓝 leading) :=
  ordinary_normalized_tendsto.comp (affine_index_tendsto k b hk)

theorem probability_even_scaled_tendsto :
    Tendsto (fun j => tilingProbability (2 * j) * growth ^ j) atTop (𝓝 (growth - 1)) := by
  have hs : Tendsto (fun j => d (j + 1) / growth ^ (j + 1)) atTop (𝓝 leading) := by
    simpa using ordinary_normalized_affine 1 1 (by decide)
  have he : Tendsto (fun j => d (2 * j) / growth ^ (2 * j)) atTop (𝓝 leading) := by
    simpa using ordinary_normalized_affine 2 0 (by decide)
  have h := (((hs.const_mul growth).sub ordinary_normalized_tendsto).sub inverse_growth_tendsto).div he (ne_of_gt leading_pos)
  have hc : (growth * leading - leading - 0) / leading = growth - 1 := by
    field_simp [growth_ne_zero, ne_of_gt leading_pos]
    ring
  rw [hc] at h
  convert h using 1
  ext j
  exact probability_even_scaled j

theorem probability_odd_scaled_tendsto :
    Tendsto (fun j => tilingProbability (2 * j + 1) * growth ^ j) atTop
      (𝓝 ((growth + 1) / growth)) := by
  have hs : Tendsto (fun j => d (j + 1) / growth ^ (j + 1)) atTop (𝓝 leading) := by
    simpa using ordinary_normalized_affine 1 1 (by decide)
  have ho := ordinary_normalized_affine 2 1 (by decide)
  have h := (((hs.const_mul growth).add ordinary_normalized_tendsto).sub inverse_growth_tendsto).div
    (ho.const_mul growth) (mul_ne_zero growth_ne_zero (ne_of_gt leading_pos))
  have hc : (growth * leading + leading - 0) / (growth * leading) = (growth + 1) / growth := by
    field_simp [growth_ne_zero, ne_of_gt leading_pos]
    ring
  rw [hc] at h
  convert h using 1
  ext j
  exact probability_odd_scaled j

theorem probability_even_asymptotic_ratio :
    Tendsto (fun j => tilingProbability (2 * j) / ((growth - 1) * decay ^ j)) atTop (𝓝 1) := by
  have h := probability_even_scaled_tendsto.div_const (growth - 1)
  simpa [decay_eq_inv, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
    ne_of_gt (sub_pos.mpr growth_gt_one)] using h

theorem probability_odd_asymptotic_ratio :
    Tendsto (fun j => tilingProbability (2 * j + 1) / (((growth + 1) / growth) * decay ^ j))
      atTop (𝓝 1) := by
  have hc : (growth + 1) / growth ≠ 0 :=
    ne_of_gt (div_pos (add_pos growth_pos zero_lt_one) growth_pos)
  have h := probability_odd_scaled_tendsto.div_const ((growth + 1) / growth)
  rw [div_self hc] at h
  convert h using 1
  ext j
  simp [decay_eq_inv, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

theorem tiling_probability_tendsto_zero : Tendsto tilingProbability atTop (𝓝 0) := by
  apply tendsto_of_even_odd
  · have h := probability_even_scaled_tendsto.mul inverse_growth_tendsto
    simpa [mul_assoc, growth_ne_zero] using h
  · have h := probability_odd_scaled_tendsto.mul inverse_growth_tendsto
    simpa [mul_assoc, growth_ne_zero] using h

end Domino.Asymptotic
