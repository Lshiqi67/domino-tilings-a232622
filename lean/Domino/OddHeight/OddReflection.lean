module

public import Domino.OddHeight.PathAction
public import Domino.OddHeight.EvenColumn
public import Domino.OddHeight.Transpose

/-! 奇数列左右反射的中央列必须无水平跨线；转置后得到奇数高度上下反射双射。 -/

@[expose] public section

namespace Domino.General

variable {m : ℕ}

abbrev OddAxialPath (m n : ℕ) :=
  {P : StatePath (m := m) (2 * n + 1) ∅ //
    ∀ k, k ≤ 2 * n + 1 → P.state k = P.state (2 * n + 1 - k)}

theorem oddAxial_center_empty {n : ℕ} (Q : OddAxialPath m n) : Q.val.state n = ∅ := by
  have hs := Q.property n (by omega)
  have he : 2 * n + 1 - n = n + 1 := by omega
  rw [he] at hs
  have step := Q.val.step n (by omega)
  rw [← hs] at step
  exact (legal_self_iff _).mp step |>.1

def restrictOddPath {n : ℕ} (Q : OddAxialPath m n) : StatePath (m := m) n ∅ where
  state k := if k ≤ n then Q.val.state k else ∅
  start := by simp [Q.val.start]
  finish := by simp [oddAxial_center_empty Q]
  support k hk := by simp [show ¬k ≤ n by omega]
  step k hk := by
    simpa [show k ≤ n by omega, show k + 1 ≤ n by omega] using Q.val.step k (by omega)

def oddDoubledState {n : ℕ} (P : StatePath (m := m) n ∅) (k : ℕ) : State m :=
  if k ≤ n then P.state k else if k ≤ 2 * n + 1 then P.state (2 * n + 1 - k) else ∅

theorem oddDoubledState_symmetric {n : ℕ} (P : StatePath (m := m) n ∅)
    (k : ℕ) (hk : k ≤ 2 * n + 1) :
    oddDoubledState P k = oddDoubledState P (2 * n + 1 - k) := by
  have hh : 2 * n + 1 - (2 * n + 1 - k) = k := by omega
  by_cases hl : k ≤ n
  · simp [oddDoubledState, hl, show ¬2 * n + 1 - k ≤ n by omega,
      show 2 * n + 1 - k ≤ 2 * n + 1 by omega, hh]
  · simp [oddDoubledState, hl, hk, show 2 * n + 1 - k ≤ n by omega]

def completeOddPath (h0 : Legal (∅ : State m) ∅) {n : ℕ}
    (P : StatePath (m := m) n ∅) : OddAxialPath m n :=
  ⟨{ state := oddDoubledState P
     start := by simp [oddDoubledState, P.start]
     finish := by simp [oddDoubledState, show ¬2 * n + 1 ≤ n by omega, P.start]
     support k hk := by simp [oddDoubledState, show ¬k ≤ n by omega, show ¬k ≤ 2 * n + 1 by omega]
     step k hk := by
       by_cases hl : k < n
       · simpa [oddDoubledState, show k ≤ n by omega, show k + 1 ≤ n by omega] using P.step k hl
       · by_cases he : k = n
         · subst k
           simpa [oddDoubledState, P.finish, show ¬n + 1 ≤ n by omega,
             show n + 1 ≤ 2 * n + 1 by omega, show 2 * n + 1 - (n + 1) = n by omega] using h0
         · have hj : 2 * n + 1 - (k + 1) < n := by omega
           have hstep := (legal_symm _ _).mp (P.step _ hj)
           rw [show 2 * n + 1 - (k + 1) + 1 = 2 * n + 1 - k by omega] at hstep
           simpa [oddDoubledState, show ¬k ≤ n by omega, show ¬k + 1 ≤ n by omega,
             show k ≤ 2 * n + 1 by omega, show k + 1 ≤ 2 * n + 1 by omega,
             show 2 * n + 1 - (k + 1) + 1 = 2 * n + 1 - k by omega] using hstep },
    oddDoubledState_symmetric P⟩

theorem restrict_complete_odd (h0 : Legal (∅ : State m) ∅) {n : ℕ}
    (P : StatePath (m := m) n ∅) : restrictOddPath (completeOddPath h0 P) = P := by
  apply statePath_ext
  funext k
  by_cases hk : k ≤ n
  · simp [restrictOddPath, completeOddPath, oddDoubledState, hk]
  · simp [restrictOddPath, hk, P.support k (by omega)]

theorem complete_restrict_odd (h0 : Legal (∅ : State m) ∅) {n : ℕ}
    (Q : OddAxialPath m n) : completeOddPath h0 (restrictOddPath Q) = Q := by
  apply Subtype.ext
  apply statePath_ext
  funext k
  change oddDoubledState (restrictOddPath Q) k = Q.val.state k
  by_cases hl : k ≤ n
  · simp [oddDoubledState, restrictOddPath, hl]
  · by_cases hk : k ≤ 2 * n + 1
    · simpa [oddDoubledState, restrictOddPath, hl, hk, show 2 * n + 1 - k ≤ n by omega]
        using (Q.property k hk).symm
    · simp [oddDoubledState, hl, hk, Q.val.support k (by omega)]

def oddAxialEquivClosed (h0 : Legal (∅ : State m) ∅) (n : ℕ) :
    OddAxialPath m n ≃ StatePath (m := m) n ∅ where
  toFun := restrictOddPath
  invFun := completeOddPath h0
  left_inv := complete_restrict_odd h0
  right_inv := restrict_complete_odd h0

noncomputable def oddReflectionFixedEquiv (h0 : Legal (∅ : State m) ∅) (k : ℕ) :
    {T : Tiling m (2 * k + 1) // vertical • T = T} ≃ Tiling m k :=
  ((tilingEquivClosedPath (m := m) (2 * k + 1)).subtypeEquiv fun T => by
    exact axial_fixed_iff_path false T).trans
    ((oddAxialEquivClosed h0 k).trans (tilingEquivClosedPath (m := m) k).symm)

noncomputable def horizontalFixedEquivTop (k n : ℕ) :
    {T : Tiling (2 * k + 1) (2 * n) // horizontal • T = T} ≃ Tiling k (2 * n) :=
  (horizontalFixedTransposeEquiv (2 * k + 1) (2 * n)).trans
    ((oddReflectionFixedEquiv (legal_empty_even n) k).trans (transposeTilingEquiv (2 * n) k))

theorem horizontal_fixed_count_odd (k n : ℕ) :
    fixedCount (2 * k + 1) n horizontal = ordinaryCount k n :=
  Fintype.card_congr (horizontalFixedEquivTop k n)

end Domino.General
