module

public import Domino.Asymptotics.OrbitLimits

/-! 使用实数幂统一奇偶指标，证明概率与轨道误差的指数 Big-O 界。 -/

@[expose] public section

namespace Domino.Asymptotic

open Filter Topology Asymptotics

noncomputable def halfGrowth (n : ℕ) : ℝ := growth ^ ((n : ℝ) / 2)
noncomputable def halfDecay (n : ℕ) : ℝ := (halfGrowth n)⁻¹
noncomputable def orbitError (n : ℕ) : ℝ := (a n : ℝ) - d n / 4

theorem halfGrowth_pos (n : ℕ) : 0 < halfGrowth n := Real.rpow_pos_of_pos growth_pos _

theorem halfDecay_rpow (n : ℕ) : halfDecay n = growth ^ (-(n : ℝ) / 2) := by
  rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring, Real.rpow_neg growth_pos.le]
  rfl

theorem halfGrowth_even (j : ℕ) : halfGrowth (2 * j) = growth ^ j := by
  simp [halfGrowth, Nat.cast_mul, Real.rpow_natCast]

theorem halfGrowth_odd (j : ℕ) : halfGrowth (2 * j + 1) = growth ^ j * growth ^ (1 / 2 : ℝ) := by
  unfold halfGrowth
  rw [show ((2 * j + 1 : ℕ) : ℝ) / 2 = (j : ℝ) + 1 / 2 by push_cast; ring,
    Real.rpow_add growth_pos, Real.rpow_natCast]

theorem isBigO_of_even_odd {f g : ℕ → ℝ}
    (he : (fun j => f (2 * j)) =O[atTop] (fun j => g (2 * j)))
    (ho : (fun j => f (2 * j + 1)) =O[atTop] (fun j => g (2 * j + 1))) :
    f =O[atTop] g := by
  obtain ⟨C, hC⟩ := he.isBigOWith
  obtain ⟨D, hD⟩ := ho.isBigOWith
  apply IsBigOWith.isBigO (c := max C D)
  apply IsBigOWith.of_bound
  exact eventually_of_even_odd (hC.weaken (le_max_left _ _)).bound
    (hD.weaken (le_max_right _ _)).bound

theorem tiling_probability_bigO : tilingProbability =O[atTop] halfDecay := by
  apply isBigO_of_even_odd
  · apply isBigO_of_div_tendsto_nhds (Eventually.of_forall fun j hj => False.elim
      ((inv_ne_zero (ne_of_gt (halfGrowth_pos (2 * j)))) hj)) (growth - 1)
    change Tendsto (fun j => tilingProbability (2 * j) / halfDecay (2 * j)) atTop _
    simpa [halfDecay, halfGrowth_even, div_eq_mul_inv] using probability_even_scaled_tendsto
  · apply isBigO_of_div_tendsto_nhds (Eventually.of_forall fun j hj => False.elim
      ((inv_ne_zero (ne_of_gt (halfGrowth_pos (2 * j + 1)))) hj))
        (((growth + 1) / growth) * growth ^ (1 / 2 : ℝ))
    change Tendsto (fun j => tilingProbability (2 * j + 1) / halfDecay (2 * j + 1)) atTop _
    simpa [halfDecay, halfGrowth_odd, div_eq_mul_inv, mul_assoc] using
      probability_odd_scaled_tendsto.mul_const (growth ^ (1 / 2 : ℝ))

theorem orbit_error_even_scaled (j : ℕ) :
    orbitError (2 * j) / growth ^ j =
      (growth * (d (j + 1) / growth ^ (j + 1)) - d j / growth ^ j + (growth ^ j)⁻¹) / 4 := by
  have h : 4 * (a (2 * j) : ℝ) + d j = d (2 * j) + 1 + d (j + 1) := by
    dsimp only [d]; exact_mod_cast orbit_even_add j
  unfold orbitError
  field_simp [growth_ne_zero, pow_succ]
  simp only [pow_succ]
  linear_combination (growth ^ j * growth) * h

theorem orbit_error_odd_scaled (j : ℕ) :
    orbitError (2 * j + 1) / growth ^ j =
      (growth * (d (j + 1) / growth ^ (j + 1)) + d j / growth ^ j + (growth ^ j)⁻¹) / 4 := by
  have h : 4 * (a (2 * j + 1) : ℝ) = d (2 * j + 1) + 1 + d (j + 1) + d j := by
    dsimp only [d]; exact_mod_cast orbit_odd_mul j
  unfold orbitError
  field_simp [growth_ne_zero, pow_succ]
  simp only [pow_succ]
  linear_combination (growth ^ j * growth) * h

theorem orbit_error_even_tendsto :
    Tendsto (fun j => orbitError (2 * j) / halfGrowth (2 * j)) atTop
      (𝓝 (leading * (growth - 1) / 4)) := by
  have hs : Tendsto (fun j => d (j + 1) / growth ^ (j + 1)) atTop (𝓝 leading) := by
    simpa using ordinary_normalized_affine 1 1 (by decide)
  have h := (((hs.const_mul growth).sub ordinary_normalized_tendsto).add inverse_growth_tendsto).div_const 4
  convert h using 1
  · ext j; rw [halfGrowth_even, orbit_error_even_scaled]
  · congr 1; ring

theorem orbit_error_odd_tendsto :
    Tendsto (fun j => orbitError (2 * j + 1) / halfGrowth (2 * j + 1)) atTop
      (𝓝 (leading * (growth + 1) / (4 * growth ^ (1 / 2 : ℝ)))) := by
  have hs : Tendsto (fun j => d (j + 1) / growth ^ (j + 1)) atTop (𝓝 leading) := by
    simpa using ordinary_normalized_affine 1 1 (by decide)
  have h := ((((hs.const_mul growth).add ordinary_normalized_tendsto).add inverse_growth_tendsto).div_const 4).div_const (growth ^ (1 / 2 : ℝ))
  convert h using 1
  · ext j; rw [halfGrowth_odd, ← div_div, orbit_error_odd_scaled]
  · congr 1; ring

theorem orbit_error_bigO : orbitError =O[atTop] halfGrowth := by
  apply isBigO_of_even_odd
  · exact isBigO_of_div_tendsto_nhds (Eventually.of_forall fun j hj => False.elim
      ((ne_of_gt (halfGrowth_pos (2 * j))) hj)) _ orbit_error_even_tendsto
  · exact isBigO_of_div_tendsto_nhds (Eventually.of_forall fun j hj => False.elim
      ((ne_of_gt (halfGrowth_pos (2 * j + 1))) hj)) _ orbit_error_odd_tendsto

end Domino.Asymptotic
