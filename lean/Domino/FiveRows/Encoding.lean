module

public import Domino.OddHeight.Boundary

/-! 有限二进制行集合编码；矩阵条目仍由已证明的几何列规则给出。 -/

@[expose] public section

namespace Domino.FiveRows

def maskState (m : ℕ) (i : Fin (2 ^ m)) : State m :=
  Finset.univ.filter fun r => i.val / 2 ^ r.val % 2 = 1

set_option maxRecDepth 4096 in
theorem maskState_five_bijective : Function.Bijective (maskState 5) := by decide

theorem maskState_two_bijective : Function.Bijective (maskState 2) := by decide

noncomputable def maskEquiv (m : ℕ) (h : Function.Bijective (maskState m)) :
    Fin (2 ^ m) ≃ State m := Equiv.ofBijective (maskState m) h

def encodedTransfer (m : ℕ) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℕ := fun q p =>
  if Disjoint (maskState m p) (maskState m q) ∧
    General.evenRunScan (fun r => decide (r ∉ (maskState m p ∪ maskState m q).image Fin.val)) false 0 m
    then 1 else 0

theorem encoded_transfer_eq (m : ℕ) (p q : Fin (2 ^ m)) :
    General.transfer (maskState m p) (maskState m q) = encodedTransfer m q p := by
  simp only [General.transfer, General.legal_iff_even_run_scan, encodedTransfer]

noncomputable def profile (m w : ℕ) (i : Fin (2 ^ m)) : ℕ :=
  General.profileCount w (maskState m i)

theorem profile_succ (m : ℕ) (h : Function.Bijective (maskState m)) (w : ℕ) :
    profile m (w + 1) = (encodedTransfer m).mulVec (profile m w) := by
  classical
  funext q
  rw [profile, General.profile_count_succ]
  rw [← (maskEquiv m h).sum_comp]
  simp only [maskEquiv, Equiv.ofBijective_apply, encoded_transfer_eq, Matrix.mulVec,
    dotProduct, profile, mul_comm]

theorem encoded_transfer_reverse (m : ℕ) (p q : State m) :
    General.transfer (reverseState p) (reverseState q) = General.transfer p q := by
  simp only [General.transfer, ← General.legal_reverse]

end Domino.FiveRows
