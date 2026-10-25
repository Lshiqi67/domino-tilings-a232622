module

public import Domino.Transfer.PathEquiv
public import Domino.Symmetry.Counting
public import Mathlib.Data.Matrix.Mul

/-! 通过路径末步的实际分拆证明几何计数递推与矩阵幂公式。 -/

@[expose] public section

namespace Domino

def pathPrefix {w : ℕ} {q : State 3} (P : StatePath (w + 1) q) : StatePath w (P.state w) where
  state k := if k ≤ w then P.state k else ∅
  start := by simp [P.start]
  finish := by simp
  support k hk := by simp [show ¬k ≤ w by omega]
  step k hk := by
    simpa [show k ≤ w by omega, show k + 1 ≤ w by omega] using P.step k (by omega)

def pathAppend {w : ℕ} {p q : State 3} (P : StatePath w p) (h : Legal3 p q) :
    StatePath (w + 1) q where
  state k := if k = w + 1 then q else P.state k
  start := by simp [P.start]
  finish := by simp
  support k hk := by simp [show k ≠ w + 1 by omega, P.support k (by omega)]
  step k hk := by
    by_cases hlast : k = w
    · subst k
      simpa [P.finish] using h
    · have hkw : k < w := by omega
      simpa [show k ≠ w + 1 by omega, hlast] using P.step k hkw

abbrev PathLast (w : ℕ) (q : State 3) := Σ p : State 3, {_P : StatePath w p // Legal3 p q}

def pathLastTo {w : ℕ} {q : State 3} (P : StatePath (w + 1) q) : PathLast w q :=
  ⟨P.state w, pathPrefix P, by simpa [P.finish] using P.step w (by omega)⟩

def pathLastFrom {w : ℕ} {q : State 3} (P : PathLast w q) : StatePath (w + 1) q :=
  pathAppend P.2.val P.2.property

theorem pathLast_from_to {w : ℕ} {q : State 3} (P : StatePath (w + 1) q) :
    pathLastFrom (pathLastTo P) = P := by
  apply statePath_ext
  funext k
  change (if k = w + 1 then q else if k ≤ w then P.state k else ∅) = P.state k
  by_cases he : k = w + 1
  · simp [he, P.finish]
  · by_cases hk : k ≤ w
    · simp [he, hk]
    · simp [he, hk, P.support k (by omega)]

theorem pathLastFrom_injective (w : ℕ) (q : State 3) :
    Function.Injective (@pathLastFrom w q) := by
  rintro ⟨p, P, hp⟩ ⟨s, Q, hs⟩ he
  have hps : p = s := by
    have := congrArg (fun A : StatePath (w + 1) q => A.state w) he
    simpa [pathLastFrom, pathAppend, P.finish, Q.finish] using this
  subst s
  have hPQ : P = Q := by
    apply statePath_ext
    funext k
    by_cases hk : k ≤ w
    · have := congrArg (fun A : StatePath (w + 1) q => A.state k) he
      simpa [pathLastFrom, pathAppend, show k ≠ w + 1 by omega] using this
    · rw [P.support k (by omega), Q.support k (by omega)]
  subst Q
  rfl

theorem pathLast_to_from {w : ℕ} {q : State 3} (P : PathLast w q) :
    pathLastTo (pathLastFrom P) = P := by
  apply pathLastFrom_injective w q
  exact pathLast_from_to (pathLastFrom P)

def pathSuccEquiv (w : ℕ) (q : State 3) : StatePath (w + 1) q ≃ PathLast w q where
  toFun := pathLastTo
  invFun := pathLastFrom
  left_inv := pathLast_from_to
  right_inv := pathLast_to_from

noncomputable def profileCount (w : ℕ) (S : State 3) : ℕ := Fintype.card (PartialTiling 3 w S)

theorem profile_count_path (w : ℕ) (S : State 3) :
    profileCount w S = Fintype.card (StatePath w S) :=
  Fintype.card_congr (partialTilingEquivPath w S)

theorem profile_count_zero (S : State 3) : profileCount 0 S = if S = ∅ then 1 else 0 :=
  partial_width_zero_card 3 S

theorem profile_count_succ (w : ℕ) (q : State 3) :
    profileCount (w + 1) q = ∑ p : State 3, profileCount w p * transfer3 p q := by
  classical
  rw [profile_count_path, Fintype.card_congr (pathSuccEquiv w q), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : Legal3 p q <;> simp [transfer3, h, profile_count_path]

def transferMatrix : Matrix (State 3) (State 3) ℕ := transfer3

theorem profile_count_matrix (w : ℕ) (S : State 3) :
    profileCount w S = (transferMatrix ^ w) ∅ S := by
  induction w generalizing S with
  | zero => simp [profile_count_zero, Matrix.one_apply, eq_comm]
  | succ w ih =>
      rw [profile_count_succ, pow_succ, Matrix.mul_apply]
      simp only [ih, transferMatrix]

theorem ordinary_count_profile (n : ℕ) : ordinaryCount 3 n = profileCount (2 * n) ∅ :=
  (partial_empty_card 3 (2 * n)).symm

theorem tiling_count_matrix (w : ℕ) : Fintype.card (Tiling 3 w) = (transferMatrix ^ w) ∅ ∅ := by
  rw [← partial_empty_card 3 w]
  exact profile_count_matrix w ∅

end Domino
