module

public import Domino.FiveRows.Encoding

/-! 全部 32 状态与六类反转轨道之间的逐列交织恒等式。 -/

@[expose] public section

namespace Domino.FiveRows

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def evenClass : Fin 6 → Finset (Fin 32) :=
  ![{0}, {3, 24}, {6, 12}, {9, 18}, {15, 30}, {27}]

def oddClass : Fin 6 → Finset (Fin 32) :=
  ![{1, 16}, {4}, {7, 28}, {13, 22}, {19, 25}, {31}]

def evenLift : Matrix (Fin 32) (Fin 6) ℕ := fun p i => if p ∈ evenClass i then 1 else 0

def oddLift : Matrix (Fin 32) (Fin 6) ℕ := fun p i => if p ∈ oddClass i then 1 else 0

def matrixB : Matrix (Fin 6) (Fin 6) ℕ :=
  ![![1, 1, 1, 1, 1, 0],
    ![1, 2, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0],
    ![1, 0, 1, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0]]

def matrixC : Matrix (Fin 6) (Fin 6) ℕ :=
  ![![2, 1, 2, 0, 2, 1],
    ![1, 1, 1, 0, 0, 0],
    ![1, 0, 0, 0, 1, 0],
    ![1, 0, 0, 1, 0, 0],
    ![1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0]]

def matrixM : Matrix (Fin 6) (Fin 6) ℕ :=
  ![![8, 6, 4, 2, 2, 1],
    ![3, 4, 1, 1, 1, 1],
    ![2, 1, 2, 1, 1, 0],
    ![1, 1, 1, 2, 1, 0],
    ![1, 1, 1, 1, 1, 0],
    ![1, 2, 0, 0, 0, 1]]

def initial : Fin 6 → ℕ := ![1, 0, 0, 0, 0, 0]

def compressed : ℕ → Fin 6 → ℕ
  | 0 => initial
  | n + 1 => matrixM.mulVec (compressed n)

theorem matrix_CB : matrixC * matrixB = matrixM := by decide

theorem transfer_even_lift : encodedTransfer 5 * evenLift = oddLift * matrixB := by decide

theorem transfer_odd_lift : encodedTransfer 5 * oddLift = evenLift * matrixC := by decide

theorem profile_initial : profile 5 0 = evenLift.mulVec initial := by
  funext p
  rw [profile, General.profile_count_zero]
  exact (show ∀ p : Fin 32, (if maskState 5 p = ∅ then 1 else 0) =
    evenLift.mulVec initial p by decide) p

theorem profile_even_odd (n : ℕ) :
    profile 5 (2 * n) = evenLift.mulVec (compressed n) ∧
    profile 5 (2 * n + 1) = oddLift.mulVec (matrixB.mulVec (compressed n)) := by
  have next (n : ℕ) (h : profile 5 (2 * n) = evenLift.mulVec (compressed n)) :
      profile 5 (2 * n + 1) = oddLift.mulVec (matrixB.mulVec (compressed n)) := by
    rw [profile_succ 5 maskState_five_bijective, h, Matrix.mulVec_mulVec,
      transfer_even_lift, ← Matrix.mulVec_mulVec]
  induction n with
  | zero => exact ⟨profile_initial, next 0 profile_initial⟩
  | succ n ih =>
    have he : profile 5 (2 * (n + 1)) = evenLift.mulVec (compressed (n + 1)) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        profile_succ 5 maskState_five_bijective, ih.2, Matrix.mulVec_mulVec,
        transfer_odd_lift, Matrix.mulVec_mulVec, Matrix.mul_assoc, matrix_CB, ← Matrix.mulVec_mulVec]
      rfl
    exact ⟨he, next (n + 1) he⟩

theorem even_class_row : ∀ (i : Fin 6) (p : Fin 32) (j : Fin 6), p ∈ evenClass i →
    evenLift p j = if i = j then 1 else 0 := by
  simp only [evenLift]
  decide

theorem odd_class_row : ∀ (i : Fin 6) (p : Fin 32) (j : Fin 6), p ∈ oddClass i →
    oddLift p j = if i = j then 1 else 0 := by
  simp only [oddLift]
  decide

theorem compressed_is_single_state_count (n : ℕ) (i : Fin 6) (p : Fin 32) (hp : p ∈ evenClass i) :
    profile 5 (2 * n) p = compressed n i := by
  rw [(profile_even_odd n).1]
  simp [Matrix.mulVec, dotProduct, fun j => even_class_row i p j hp]

theorem compressed_odd_is_single_state_count (n : ℕ) (i : Fin 6) (p : Fin 32) (hp : p ∈ oddClass i) :
    profile 5 (2 * n + 1) p = matrixB.mulVec (compressed n) i := by
  rw [(profile_even_odd n).2]
  simp [Matrix.mulVec, dotProduct, fun j => odd_class_row i p j hp]

theorem classes_are_reverse_orbits :
    (∀ i p q, p ∈ evenClass i → q ∈ evenClass i →
      maskState 5 q = maskState 5 p ∨ maskState 5 q = reverseState (maskState 5 p)) ∧
    (∀ i p q, p ∈ oddClass i → q ∈ oddClass i →
      maskState 5 q = maskState 5 p ∨ maskState 5 q = reverseState (maskState 5 p)) := by decide

def evenSupport : Finset (Fin 32) := Finset.univ.biUnion evenClass

def oddSupport : Finset (Fin 32) := Finset.univ.biUnion oddClass

theorem support_cards : evenSupport.card = 10 ∧ oddSupport.card = 10 := by decide

theorem support_closed :
    (∀ p q, p ∈ evenSupport → encodedTransfer 5 q p ≠ 0 → q ∈ oddSupport) ∧
    (∀ p q, p ∈ oddSupport → encodedTransfer 5 q p ≠ 0 → q ∈ evenSupport) := by decide

theorem profile_reverse (n : ℕ) (p q : Fin 32) (h : maskState 5 q = reverseState (maskState 5 p)) :
    profile 5 n q = profile 5 n p := by
  have he : ∀ (p q : Fin 32) (i : Fin 6), maskState 5 q = reverseState (maskState 5 p) → evenLift q i = evenLift p i := by
    simp only [evenLift]
    decide
  have ho : ∀ (p q : Fin 32) (i : Fin 6), maskState 5 q = reverseState (maskState 5 p) → oddLift q i = oddLift p i := by
    simp only [oddLift]
    decide
  have hn : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1 := by omega
  rcases hn with hn | hn
  · rw [hn, (profile_even_odd _).1]; simp only [Matrix.mulVec, dotProduct, fun i => he p q i h]
  · rw [hn, (profile_even_odd _).2]; simp only [Matrix.mulVec, dotProduct, fun i => ho p q i h]

end Domino.FiveRows
