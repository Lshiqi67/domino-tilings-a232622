module

public import Domino.Blocks.Decomposition

/-! 基本块字与原始几何铺法的保权双射；有限性由实际棋盘有限性推出。 -/

@[expose] public section
namespace Domino.Blocks

theorem valid_iff_getD (p : State 3) (L : List (State 3)) :
    Valid p L ↔ (p :: L).getD L.length ∅ = ∅ ∧
      ∀ k, k < L.length → Legal3 ((p :: L).getD k ∅) ((p :: L).getD (k + 1) ∅) := by
  induction L generalizing p with
  | nil => simp [Valid]
  | cons q L ih =>
    constructor
    · rintro ⟨hp,hq⟩
      obtain ⟨hf,hs⟩ := (ih q).mp hq
      refine ⟨by simpa using hf,?_⟩
      intro k hk
      cases k with
      | zero => simpa using hp
      | succ k => simpa using hs k (by simpa using hk)
    · rintro ⟨hf,hs⟩
      refine ⟨by simpa using hs 0 (by simp), (ih q).mpr ⟨by simpa using hf,?_⟩⟩
      intro k hk
      simpa using hs (k+1) (by simpa using hk)

def pathList {w : ℕ} (P : StatePath w ∅) : List (State 3) :=
  List.ofFn fun i : Fin w => P.state (i.val + 1)

@[simp] theorem pathList_length {w : ℕ} (P : StatePath w ∅) : (pathList P).length = w := by simp [pathList]

theorem pathList_getD {w : ℕ} (P : StatePath w ∅) (k : ℕ) :
    (∅ :: pathList P).getD k ∅ = P.state k := by
  cases k with
  | zero => simpa using P.start.symm
  | succ k =>
    change (pathList P).getD k ∅ = P.state (k+1)
    by_cases hk : k < w
    · rw [List.getD_eq_getElem _ _ (by simpa using hk)]
      simp [pathList]
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hk)]
      exact (P.support _ (by omega)).symm

theorem pathList_valid {w : ℕ} (P : StatePath w ∅) : Valid ∅ (pathList P) := by
  rw [valid_iff_getD, pathList_length]
  simp only [pathList_getD]
  exact ⟨P.finish,P.step⟩

def pathOfList (w : ℕ) (L : List (State 3)) (hl : L.length = w) (hv : Valid ∅ L) : StatePath w ∅ where
  state k := (∅ :: L).getD k ∅
  start := by simp
  finish := by rw [← hl]; exact ((valid_iff_getD ∅ L).mp hv).1
  support k hk := List.getD_eq_default _ _ (by simp [hl]; omega)
  step k hk := ((valid_iff_getD ∅ L).mp hv).2 k (by omega)

theorem list_getD_ext (L K : List (State 3)) (hl : L.length = K.length)
    (h : ∀ k, L.getD k ∅ = K.getD k ∅) : L = K := by
  apply List.ext_getElem hl
  intro k hk hk'
  simpa only [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk'] using h k

@[simp] theorem pathList_pathOfList (w : ℕ) (L : List (State 3)) (hl : L.length = w) (hv : Valid ∅ L) :
    pathList (pathOfList w L hl hv) = L := by
  apply list_getD_ext _ _ (by simp [hl])
  intro k
  have h := pathList_getD (pathOfList w L hl hv) (k+1)
  simpa only [pathOfList, List.getD_cons_succ] using h

@[simp] theorem pathOfList_pathList {w : ℕ} (P : StatePath w ∅) :
    pathOfList w (pathList P) (pathList_length P) (pathList_valid P) = P := by
  apply statePath_ext
  funext k
  exact pathList_getD P k

abbrev Word (n : ℕ) := {W : List Letter // mass W = n}

def wordPath {n : ℕ} (W : Word n) : StatePath (2*n) ∅ :=
  pathOfList (2*n) (trace W.val) (by simp [W.property]) (valid_trace W.val)

def pathWord {n : ℕ} (P : StatePath (2*n) ∅) : Word n :=
  ⟨decode (pathList P), by
    have h := congrArg List.length (valid_decode (pathList P) (pathList_valid P))
    simp only [trace_length,pathList_length] at h
    omega⟩

@[simp] theorem wordPath_pathWord {n : ℕ} (P : StatePath (2*n) ∅) : wordPath (pathWord P) = P := by
  apply statePath_ext
  funext k
  change (∅ :: trace (decode (pathList P))).getD k ∅ = _
  rw [valid_decode _ (pathList_valid P),pathList_getD]

@[simp] theorem pathWord_wordPath {n : ℕ} (W : Word n) : pathWord (wordPath W) = W := by
  apply Subtype.ext
  change decode (pathList (pathOfList _ _ _ _)) = W.val
  rw [pathList_pathOfList,decode_trace]

def wordEquivPath (n : ℕ) : Word n ≃ StatePath (2*n) ∅ where
  toFun := wordPath
  invFun := pathWord
  left_inv := pathWord_wordPath
  right_inv := wordPath_pathWord

noncomputable def wordEquivTiling (n : ℕ) : Word n ≃ Tiling 3 (2*n) :=
  (wordEquivPath n).trans (tilingEquivClosedPath (2*n)).symm

instance wordFinite (n : ℕ) : Finite (Word n) := Finite.of_equiv _ (wordEquivTiling n).symm
noncomputable instance wordFintype (n : ℕ) : Fintype (Word n) := Fintype.ofFinite _

@[simp] theorem word_card (n : ℕ) : Fintype.card (Word n) = ordinaryCount 3 n := by
  exact Fintype.card_congr (wordEquivTiling n)

theorem tiling_word_roundtrip (n : ℕ) (T : Tiling 3 (2*n)) :
    wordEquivTiling n ((wordEquivTiling n).symm T) = T := (wordEquivTiling n).apply_symm_apply T

theorem word_tiling_roundtrip (n : ℕ) (W : Word n) :
    (wordEquivTiling n).symm (wordEquivTiling n W) = W := (wordEquivTiling n).symm_apply_apply W

end Domino.Blocks
