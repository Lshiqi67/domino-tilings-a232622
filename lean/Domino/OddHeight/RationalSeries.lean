module

public import Domino.OddHeight.MatrixSeries

@[expose] public section

namespace Domino.General

open PowerSeries

theorem rational_zero : RationalSeries 0 := ⟨0, 1, by simp, by simp⟩

theorem rational_add {F G : PowerSeries ℚ} (hF : RationalSeries F) (hG : RationalSeries G) :
    RationalSeries (F + G) := by
  obtain ⟨P, Q, hQ, he⟩ := hF
  obtain ⟨R, S, hS, hf⟩ := hG
  refine ⟨P * S + R * Q, Q * S, ?_, ?_⟩
  · simpa [Polynomial.mul_coeff_zero] using mul_ne_zero hQ hS
  · push_cast
    calc
      (Q : PowerSeries ℚ) * S * (F + G) = (Q * F) * S + (S * G) * Q := by ring
      _ = _ := by rw [he, hf]

theorem rational_scale {F : PowerSeries ℚ} (hF : RationalSeries F) (c : ℚ) :
    RationalSeries (C c * F) := by
  obtain ⟨P, Q, hQ, he⟩ := hF
  refine ⟨Polynomial.C c * P, Q, hQ, ?_⟩
  push_cast
  rw [mul_left_comm, he]

theorem rational_sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, RationalSeries (F i)) : RationalSeries (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rational_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact rational_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem polynomial_series_coeff (Q : Polynomial ℚ) (F : PowerSeries ℚ) (N : ℕ)
    (hN : Q.natDegree ≤ N) :
    coeff N ((Q : PowerSeries ℚ) * F) =
      ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * coeff (N - i) F := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i hi hn
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp only [Finset.mem_range] at hn; omega), zero_mul]

theorem rational_eventual_recurrence {F : PowerSeries ℚ} (hF : RationalSeries F) :
    ∃ (d N : ℕ) (c : ℕ → ℚ), c 0 ≠ 0 ∧
      ∀ n, N ≤ n → coeff (n + d) F =
        -(c 0)⁻¹ * ∑ i ∈ Finset.range d, c (i + 1) * coeff (n + d - (i + 1)) F := by
  obtain ⟨P, Q, hQ, he⟩ := hF
  refine ⟨Q.natDegree, P.natDegree + 1, Q.coeff, hQ, ?_⟩
  intro n hn
  have h := congrArg (coeff (n + Q.natDegree)) he
  rw [polynomial_series_coeff Q F _ (by omega), Polynomial.coeff_coe,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Finset.sum_range_succ'] at h
  simp only [Nat.sub_zero] at h
  field_simp
  linarith [h]

end Domino.General
