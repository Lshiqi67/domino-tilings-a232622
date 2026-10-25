module

public import Domino.Asymptotics.ErrorBounds

/-! M10 汇总出口。所有计数均来自已定义的真实铺法或其轨道。 -/

@[expose] public section

namespace Domino.Asymptotic

open Filter Topology Asymptotics

theorem probabilities_two : tilingProbability 2 = 7 / 11 ∧ orbitProbability 2 = 4 / 5 := by
  have hv : fixedCount 3 2 vertical = 5 := by
    change fixedCount 3 (2 * 1) vertical = 5
    rw [reflection_even]
    norm_num [ordinary_eq_alpha, alpha, profilePair]
  have hr : fixedCount 3 2 halfTurn = 3 := by
    change fixedCount 3 (2 * 1) halfTurn = 3
    rw [halfTurn_even, ordinary_initial_values.2]
  have hd : ordinaryCount 3 2 = 11 := by norm_num [ordinary_eq_alpha, alpha, profilePair]
  norm_num [tiling_probability_formula, orbit_probability_formula, hv, hr, hd, a_two]

theorem ordinary_closed_form_paper (n : ℕ) :
    (ordinaryCount 3 n : ℝ) = leading * growth ^ n + trailing * (growth ^ n)⁻¹ := by
  simpa only [d, decay_eq_inv, inv_pow] using ordinary_closed_form n

theorem ordinary_asymptotic : d ~[atTop] (fun n => leading * growth ^ n) :=
  isEquivalent_of_tendsto_one ordinary_asymptotic_ratio

theorem probability_even_asymptotic :
    (fun j => tilingProbability (2 * j)) ~[atTop] (fun j => (growth - 1) * decay ^ j) :=
  isEquivalent_of_tendsto_one probability_even_asymptotic_ratio

theorem probability_odd_asymptotic :
    (fun j => tilingProbability (2 * j + 1)) ~[atTop] (fun j => ((growth + 1) / growth) * decay ^ j) :=
  isEquivalent_of_tendsto_one probability_odd_asymptotic_ratio

theorem orbit_asymptotic :
    (fun n => (a n : ℝ)) ~[atTop] (fun n => (leading / 4) * growth ^ n) :=
  isEquivalent_of_tendsto_one orbit_asymptotic_ratio

theorem probability_exponential_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      tilingProbability n ≤ C * growth ^ (-(n : ℝ) / 2) := by
  obtain ⟨C, hC, h⟩ := tiling_probability_bigO.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 h.bound
  refine ⟨C, hC, N, fun n hn => ?_⟩
  have hp := (probabilities_mem_unit_interval n).1
  have hg : 0 ≤ halfDecay n := inv_nonneg.mpr (halfGrowth_pos n).le
  have hh := hN n hn
  simp only [Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hg] at hh
  simpa only [halfDecay_rpow] using hh

theorem orbit_exponential_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      |(a n : ℝ) - (ordinaryCount 3 n : ℝ) / 4| ≤ C * growth ^ ((n : ℝ) / 2) := by
  obtain ⟨C, hC, h⟩ := orbit_error_bigO.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 h.bound
  refine ⟨C, hC, N, fun n hn => ?_⟩
  have hh := hN n hn
  simp only [Real.norm_eq_abs, abs_of_pos (halfGrowth_pos n)] at hh
  simpa only [halfGrowth, orbitError, d] using hh

theorem symmetric_tiling_probability_asymptotics :
    ((fun j => tilingProbability (2 * j)) ~[atTop] (fun j => (growth - 1) * decay ^ j)) ∧
    ((fun j => tilingProbability (2 * j + 1)) ~[atTop] (fun j => ((growth + 1) / growth) * decay ^ j)) ∧
    tilingProbability =O[atTop] halfDecay ∧ Tendsto tilingProbability atTop (𝓝 0) :=
  ⟨probability_even_asymptotic, probability_odd_asymptotic,
    tiling_probability_bigO, tiling_probability_tendsto_zero⟩

theorem orbit_count_asymptotics :
    orbitError =O[atTop] halfGrowth ∧
    (fun n => (a n : ℝ)) ~[atTop] (fun n => (leading / 4) * growth ^ n) :=
  ⟨orbit_error_bigO, orbit_asymptotic⟩

theorem symmetric_orbit_probability_tendsto_zero : Tendsto orbitProbability atTop (𝓝 0) :=
  orbit_probability_tendsto_zero

theorem three_row_asymptotic_main :
    (∀ n, (ordinaryCount 3 n : ℝ) = leading * growth ^ n + trailing * (growth ^ n)⁻¹) ∧
    (∀ n, 0 ≤ tilingProbability n ∧ tilingProbability n ≤ 1 ∧
      0 ≤ orbitProbability n ∧ orbitProbability n ≤ 1) ∧
    tilingProbability =O[atTop] halfDecay ∧ orbitError =O[atTop] halfGrowth ∧
    ((fun n => (a n : ℝ)) ~[atTop] (fun n => (leading / 4) * growth ^ n)) ∧
    Tendsto tilingProbability atTop (𝓝 0) ∧ Tendsto orbitProbability atTop (𝓝 0) :=
  ⟨ordinary_closed_form_paper, probabilities_mem_unit_interval, tiling_probability_bigO,
    orbit_error_bigO, orbit_asymptotic, tiling_probability_tendsto_zero, orbit_probability_tendsto_zero⟩

end Domino.Asymptotic
