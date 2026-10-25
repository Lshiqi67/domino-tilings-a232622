module

public import Domino.Symmetry.PathAction

/-! 带可选行反转的半路径补全；中线兼容只约束终端集合。 -/

@[expose] public section

namespace Domino

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem legal3_twist_reverse : ∀ (b : Bool) (p q : State 3),
    Legal3 p q ↔ Legal3 (twistState b q) (twistState b p) := by decide

abbrev HalfPath (b : Bool) (n : ℕ) :=
  Σ S : {S : State 3 // twistState b S = S}, StatePath n S.val

abbrev AxialPath (b : Bool) (n : ℕ) :=
  {P : StatePath (2 * n) ∅ // ∀ k, k ≤ 2 * n → P.state k = twistState b (P.state (2 * n - k))}

theorem halfPath_ext {b : Bool} {n : ℕ} (P Q : HalfPath b n)
    (h : P.2.state = Q.2.state) : P = Q := by
  rcases P with ⟨⟨S, hS⟩, P⟩
  rcases Q with ⟨⟨R, hR⟩, Q⟩
  have he : S = R := P.finish.symm.trans ((congrFun h n).trans Q.finish)
  subst R
  have hPQ : P = Q := statePath_ext _ _ h
  subst Q
  rfl

def doubledState {b : Bool} {n : ℕ} (P : HalfPath b n) (k : ℕ) : State 3 :=
  if k ≤ n then P.2.state k else if k ≤ 2 * n then twistState b (P.2.state (2 * n - k)) else ∅

theorem doubledState_left {b : Bool} {n : ℕ} (P : HalfPath b n) (k : ℕ) (hk : k ≤ n) :
    doubledState P k = P.2.state k := by simp [doubledState, hk]

theorem doubledState_right {b : Bool} {n : ℕ} (P : HalfPath b n) (k : ℕ)
    (hk : n ≤ k) (hkw : k ≤ 2 * n) :
    doubledState P k = twistState b (P.2.state (2 * n - k)) := by
  by_cases he : k = n
  · subst k
    have hn : 2 * n - n = n := by omega
    simp only [doubledState, le_refl, ↓reduceIte, hn, P.2.finish]
    exact P.1.property.symm
  · simp [doubledState, show ¬k ≤ n by omega, hkw]

theorem doubledState_symmetric {b : Bool} {n : ℕ} (P : HalfPath b n)
    (k : ℕ) (hk : k ≤ 2 * n) :
    doubledState P k = twistState b (doubledState P (2 * n - k)) := by
  have hh : 2 * n - (2 * n - k) = k := by omega
  by_cases hl : k ≤ n
  · rw [doubledState_left P k hl, doubledState_right P (2 * n - k) (by omega) (by omega), hh,
      twistState_twice]
  · rw [doubledState_right P k (by omega) hk, doubledState_left P (2 * n - k) (by omega)]

def completeHalfPath {b : Bool} {n : ℕ} (P : HalfPath b n) : AxialPath b n :=
  ⟨{ state := doubledState P
     start := by rw [doubledState_left P 0 (by omega), P.2.start]
     finish := by
       rw [doubledState_right P (2 * n) (by omega) (by omega), Nat.sub_self,
         P.2.start, twistState_empty]
     support := fun k hk => by simp [doubledState, show ¬k ≤ n by omega, show ¬k ≤ 2 * n by omega]
     step := by
       intro k hk
       by_cases hl : k < n
       · rw [doubledState_left P k (by omega), doubledState_left P (k + 1) (by omega)]
         exact P.2.step k hl
       · rw [doubledState_right P k (by omega) (by omega),
           doubledState_right P (k + 1) (by omega) (by omega)]
         have hj : 2 * n - (k + 1) < n := by omega
         have he : 2 * n - (k + 1) + 1 = 2 * n - k := by omega
         exact (legal3_twist_reverse b _ _).mp (by simpa [he] using P.2.step _ hj) },
    doubledState_symmetric P⟩

def restrictAxialPath {b : Bool} {n : ℕ} (Q : AxialPath b n) : HalfPath b n :=
  ⟨⟨Q.val.state n, by
      have h := Q.property n (by omega)
      have hn : 2 * n - n = n := by omega
      exact (by simpa [hn] using h.symm)⟩,
   { state := fun k => if k ≤ n then Q.val.state k else ∅
     start := by simp [Q.val.start]
     finish := by simp
     support := fun k hk => by simp [show ¬k ≤ n by omega]
     step := by
       intro k hk
       simpa [show k ≤ n by omega, show k + 1 ≤ n by omega] using Q.val.step k (by omega) }⟩

theorem restrict_complete_halfPath {b : Bool} {n : ℕ} (P : HalfPath b n) :
    restrictAxialPath (completeHalfPath P) = P := by
  apply halfPath_ext
  funext k
  change (if k ≤ n then doubledState P k else ∅) = P.2.state k
  by_cases hk : k ≤ n
  · simp [hk, doubledState_left P k hk]
  · simp [hk, P.2.support k (by omega)]

theorem complete_restrict_axialPath {b : Bool} {n : ℕ} (Q : AxialPath b n) :
    completeHalfPath (restrictAxialPath Q) = Q := by
  apply Subtype.ext
  apply statePath_ext
  funext k
  change doubledState (restrictAxialPath Q) k = Q.val.state k
  by_cases hl : k ≤ n
  · simp [doubledState_left _ k hl, restrictAxialPath, hl]
  · by_cases hk : k ≤ 2 * n
    · rw [doubledState_right _ k (by omega) hk]
      simp only [restrictAxialPath, show 2 * n - k ≤ n by omega, ↓reduceIte]
      exact (Q.property k hk).symm
    · simp [doubledState, hl, hk, Q.val.support k (by omega)]

def halfPathEquivAxialPath (b : Bool) (n : ℕ) : HalfPath b n ≃ AxialPath b n where
  toFun := completeHalfPath
  invFun := restrictAxialPath
  left_inv := restrict_complete_halfPath
  right_inv := complete_restrict_axialPath

abbrev AxialFixed (b : Bool) (n : ℕ) :=
  {T : Tiling 3 (2 * n) // axialSymmetry b • T = T}

noncomputable def axialFixedEquivPath (b : Bool) (n : ℕ) : AxialFixed b n ≃ AxialPath b n where
  toFun T := ⟨tilingPath T.val, (axial_fixed_iff_path b T.val).mp T.property⟩
  invFun P := ⟨(tilingEquivClosedPath (2 * n)).symm P.val,
    (axial_fixed_iff_path b _).mpr (by
      simpa only [tilingPath, Equiv.apply_symm_apply] using P.property)⟩
  left_inv T := Subtype.ext ((tilingEquivClosedPath (2 * n)).symm_apply_apply T.val)
  right_inv P := Subtype.ext ((tilingEquivClosedPath (2 * n)).apply_symm_apply P.val)

abbrev HalfPartial (b : Bool) (n : ℕ) :=
  Σ S : {S : State 3 // twistState b S = S}, PartialTiling 3 n S.val

noncomputable def halfPartialEquivPath (b : Bool) (n : ℕ) : HalfPartial b n ≃ HalfPath b n :=
  Equiv.sigmaCongrRight fun S => partialTilingEquivPath n S.val

noncomputable def axialFixedEquivPartial (b : Bool) (n : ℕ) :
    AxialFixed b n ≃ HalfPartial b n :=
  (axialFixedEquivPath b n).trans ((halfPathEquivAxialPath b n).symm.trans
    (halfPartialEquivPath b n).symm)

end Domino
