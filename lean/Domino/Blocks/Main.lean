module

public import Domino.Blocks.Horizontal
public import Domino.Blocks.Boundary
public import Domino.Symmetry.Burnside

/-! T01：基本块路线独立得到真实轨道生成函数，只共享 Burnside 与纯代数。 -/

@[expose] public section
namespace Domino.Blocks
open PowerSeries

theorem ordinary_series_via_blocks : ordinaryDenom * countSeries (ordinaryCount 3) = 1-X := by
  rw [← wordSeries_actual]
  exact word_ordinary_identity

theorem doubled_word_identity : parityDenom * doubleSeries wordSeries = 1-X^2 := by
  have h := congrArg doubleSeries word_ordinary_identity
  simp only [map_mul,map_sub,map_one] at h
  rw [double_ordinaryDenom] at h
  simpa only [doubleSeries,expand_X] using h

theorem vertical_series_via_blocks :
    parityDenom * countSeries (fun n => fixedCount 3 n vertical) = 1+3*X+X^2-X^3 := by
  rw [vertical_word_series]
  calc
    parityDenom * ((1+letterSeries)*doubleSeries wordSeries) =
      (1+letterSeries)*(parityDenom*doubleSeries wordSeries) := by ring
    _ = (1+letterSeries)*(1-X^2) := by rw [doubled_word_identity]
    _ = _ := by linear_combination (1+X)*letter_series_identity

theorem halfTurn_series_via_blocks :
    parityDenom * countSeries (fun n => fixedCount 3 n halfTurn) = 1+X-X^2-X^3 := by
  rw [halfTurn_word_series]
  calc
    parityDenom * ((1+X)*doubleSeries wordSeries) = (1+X)*(parityDenom*doubleSeries wordSeries) := by ring
    _ = (1+X)*(1-X^2) := by rw [doubled_word_identity]
    _ = _ := by ring

theorem burnside_series_via_blocks :
    4 * countSeries a = countSeries (ordinaryCount 3) + countSeries (fun n => fixedCount 3 n horizontal) +
      countSeries (fun n => fixedCount 3 n vertical) + countSeries (fun n => fixedCount 3 n halfTurn) := by
  ext n
  simp only [coeff_ofNat_mul,map_add,coeff_countSeries]
  exact_mod_cast four_mul_orbitCount 3 n

theorem orbit_series_identity_via_blocks : orbitDenom * countSeries a = orbitNumerator := by
  have h : 4 * (orbitDenom * countSeries a) = 4 * orbitNumerator := by
    unfold orbitDenom
    linear_combination
      (1-X)*ordinaryDenom*parityDenom*burnside_series_via_blocks +
      (1-X)*parityDenom*ordinary_series_via_blocks +
      ordinaryDenom*parityDenom*horizontal_series_via_words +
      (1-X)*ordinaryDenom*vertical_series_via_blocks +
      (1-X)*ordinaryDenom*halfTurn_series_via_blocks + common_numerator_identity
  ext n
  have hc := congrArg (coeff n) h
  simp only [coeff_ofNat_mul] at hc
  linarith

theorem orbit_series_via_blocks : countSeries a = orbitNumerator * orbitDenom⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by simp : constantCoeff orbitDenom ≠ 0)).2
  simpa only [mul_comm] using orbit_series_identity_via_blocks

theorem orbit_series_paper_via_blocks :
    countSeries a = (-1+3*X+4*X^2-10*X^3+4*X^5-X^6) *
      ((X-1)*(X^2-4*X+1)*(X^4-4*X^2+1))⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by simp :
    constantCoeff ((X-1)*(X^2-4*X+1)*(X^4-4*X^2+1) : PowerSeries ℚ) ≠ 0)).2
  have h := orbit_series_identity_via_blocks
  unfold orbitDenom ordinaryDenom parityDenom orbitNumerator at h
  linear_combination -h

theorem letter_series_rational : letterSeries = (3*X-X^2)*(1-X)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by simp : constantCoeff (1-X : PowerSeries ℚ) ≠ 0)).2
  simpa only [mul_comm] using letter_series_identity

theorem word_series_rational : wordSeries = (1-X)*ordinaryDenom⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by simp [ordinaryDenom] : constantCoeff ordinaryDenom ≠ 0)).2
  simpa only [mul_comm] using word_ordinary_identity

theorem three_row_block_main :
    (∀ L, Irreducible L ↔ ∃! a, trace [a]=L) ∧
    (∀ n, Nonempty (Word n ≃ Tiling 3 (2*n))) ∧
    (∀ b W, mirror b W=W → ∃! p : List Letter × Option Letter,
      CenterOK b p.2 ∧ assemble b p.1 p.2=W) ∧
    countSeries a = orbitNumerator * orbitDenom⁻¹ :=
  ⟨irreducible_iff_letter,fun n => ⟨wordEquivTiling n⟩,palindrome_unique,orbit_series_via_blocks⟩

end Domino.Blocks
