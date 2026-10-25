module

public import Domino.FiveRows.Compression

@[expose] public section

namespace Domino.FiveRows

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def fixedWeight (p : Fin 32) : ℕ := if reverseState (maskState 5 p) = maskState 5 p then 1 else 0

def weightVE : Fin 6 → ℕ := ![1, 2, 2, 2, 2, 1]

def weightVO : Fin 6 → ℕ := ![8, 6, 4, 4, 2, 1]

def weightRE : Fin 6 → ℕ := ![1, 0, 0, 0, 0, 1]

def weightRO : Fin 6 → ℕ := ![2, 2, 0, 0, 0, 1]

theorem terminal_weights :
    Matrix.vecMul (fun _ : Fin 32 => 1) evenLift = weightVE ∧
    Matrix.vecMul (Matrix.vecMul (fun _ : Fin 32 => 1) oddLift) matrixB = weightVO ∧
    Matrix.vecMul fixedWeight evenLift = weightRE ∧
    Matrix.vecMul (Matrix.vecMul fixedWeight oddLift) matrixB = weightRO := by decide

theorem ordinary_compressed (n : ℕ) : ordinaryCount 5 n = compressed n 0 := by
  rw [General.ordinary_count_profile]
  have h := compressed_is_single_state_count n 0 0 (by decide)
  exact h

theorem reflection_encoded (n : ℕ) : fixedCount 5 n vertical = (fun _ : Fin 32 => 1) ⬝ᵥ profile 5 n := by
  classical
  rw [General.reflection_fixed_count, ← (maskEquiv 5 maskState_five_bijective).sum_comp]
  simp only [dotProduct, one_mul, profile, maskEquiv, Equiv.ofBijective_apply]
  rfl

theorem halfTurn_encoded (n : ℕ) : fixedCount 5 n halfTurn = fixedWeight ⬝ᵥ profile 5 n := by
  classical
  rw [General.halfTurn_fixed_count]
  have h : (∑ S : General.SymmetricTerminal 5, General.profileCount n S.val) =
      ∑ S : State 5, if reverseState S = S then General.profileCount n S else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  rw [h, ← (maskEquiv 5 maskState_five_bijective).sum_comp]
  simp only [dotProduct, fixedWeight, profile, maskEquiv, Equiv.ofBijective_apply,
    ite_mul, one_mul, zero_mul]
  rfl

theorem fixed_counts_compressed (n : ℕ) :
    fixedCount 5 (2 * n) vertical = weightVE ⬝ᵥ compressed n ∧
    fixedCount 5 (2 * n + 1) vertical = weightVO ⬝ᵥ compressed n ∧
    fixedCount 5 (2 * n) halfTurn = weightRE ⬝ᵥ compressed n ∧
    fixedCount 5 (2 * n + 1) halfTurn = weightRO ⬝ᵥ compressed n := by
  rw [reflection_encoded, reflection_encoded, halfTurn_encoded, halfTurn_encoded,
    (profile_even_odd n).1, (profile_even_odd n).2]
  simp only [Matrix.dotProduct_mulVec, terminal_weights.1, terminal_weights.2.1,
    terminal_weights.2.2.1, terminal_weights.2.2.2, and_self]

theorem even_reachable_iff (p : Fin 32) :
    (∃ n, 0 < profile 5 (2 * n) p) ↔ p ∈ evenSupport := by
  have hz : ∀ (p : Fin 32) (i : Fin 6), p ∉ evenSupport → evenLift p i = 0 := by
    simp only [evenLift]
    decide
  constructor
  · rintro ⟨n, hn⟩
    by_contra hp
    rw [(profile_even_odd n).1] at hn
    simp only [Matrix.mulVec, dotProduct, fun i => hz p i hp, zero_mul, Finset.sum_const_zero] at hn
    omega
  · intro hp
    refine ⟨1, ?_⟩
    rw [(profile_even_odd 1).1]
    exact (show ∀ p : Fin 32, p ∈ evenSupport → 0 < evenLift.mulVec (compressed 1) p by decide) p hp

theorem odd_reachable_iff (p : Fin 32) :
    (∃ n, 0 < profile 5 (2 * n + 1) p) ↔ p ∈ oddSupport := by
  have hz : ∀ (p : Fin 32) (i : Fin 6), p ∉ oddSupport → oddLift p i = 0 := by
    simp only [oddLift]
    decide
  constructor
  · rintro ⟨n, hn⟩
    by_contra hp
    rw [(profile_even_odd n).2] at hn
    simp only [Matrix.mulVec, dotProduct, fun i => hz p i hp, zero_mul, Finset.sum_const_zero] at hn
    omega
  · intro hp
    refine ⟨1, ?_⟩
    rw [(profile_even_odd 1).2]
    exact (show ∀ p : Fin 32, p ∈ oddSupport →
      0 < oddLift.mulVec (matrixB.mulVec (compressed 1)) p by decide) p hp

end Domino.FiveRows
