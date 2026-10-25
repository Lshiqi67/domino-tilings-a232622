module

public import Domino.Blocks.Geometry

/-! A04：真实坐标作用对应逐字母对合、倒序和二者复合。 -/

@[expose] public section
namespace Domino.Blocks

def hWord {n : ℕ} (W : Word n) : Word n := ⟨W.val.map flip, by simp [W.property]⟩
def vWord {n : ℕ} (W : Word n) : Word n := ⟨W.val.reverse, by simp [W.property]⟩
def rWord {n : ℕ} (W : Word n) : Word n := hWord (vWord W)

@[simp] theorem word_tiling_path {n : ℕ} (W : Word n) :
    tilingPath (wordEquivTiling n W) = wordPath W := by
  exact (tilingEquivClosedPath (2*n)).apply_symm_apply (wordPath W)

theorem word_horizontal {n : ℕ} (W : Word n) :
    horizontal • wordEquivTiling n W = wordEquivTiling n (hWord W) := by
  apply (tilingEquivClosedPath (2*n)).injective
  apply statePath_ext
  funext k
  change (tilingPath (horizontal • wordEquivTiling n W)).state k = (tilingPath _).state k
  rw [tilingPath_horizontal, word_tiling_path, word_tiling_path]
  change reverseState ((∅ :: trace W.val).getD k ∅) = (∅ :: trace (W.val.map flip)).getD k ∅
  rw [← trace_flip]
  simpa using (List.getD_map (∅ :: trace W.val) ∅ reverseState (n := k)).symm

theorem word_vertical {n : ℕ} (W : Word n) :
    vertical • wordEquivTiling n W = wordEquivTiling n (vWord W) := by
  apply (tilingEquivClosedPath (2*n)).injective
  apply statePath_ext
  funext k
  change (tilingPath (vertical • wordEquivTiling n W)).state k = (tilingPath _).state k
  by_cases hk : k ≤ 2*n
  · rw [tilingPath_vertical _ k hk, word_tiling_path,word_tiling_path]
    have h := congrFun (List.getD_reverse (l := ∅ :: trace W.val) k (by simp [W.property]; omega)) ∅
    rw [full_reverse] at h
    simpa [wordPath,pathOfList,vWord,W.property] using h.symm
  · rw [(tilingPath _).support k (by omega),(tilingPath _).support k (by omega)]

theorem word_halfTurn {n : ℕ} (W : Word n) :
    halfTurn • wordEquivTiling n W = wordEquivTiling n (rWord W) := by
  rw [← horizontal_mul_vertical, mul_smul, word_vertical,word_horizontal]
  rfl

def fixedEquiv {α β : Type*} (e : α ≃ β) (f : α → α) (g : β → β)
    (h : ∀ x, g (e x) = e (f x)) : {x // f x = x} ≃ {y // g y = y} where
  toFun x := ⟨e x.val, by rw [h,x.property]⟩
  invFun y := ⟨e.symm y.val, by
    apply e.injective
    rw [← h,e.apply_symm_apply,y.property]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)

noncomputable def horizontalWordEquiv (n : ℕ) :
    {W : Word n // hWord W = W} ≃ ↥(MulAction.fixedBy (Tiling 3 (2*n)) horizontal) :=
  fixedEquiv (wordEquivTiling n) hWord (horizontal • ·) word_horizontal

noncomputable def verticalWordEquiv (n : ℕ) :
    {W : Word n // vWord W = W} ≃ ↥(MulAction.fixedBy (Tiling 3 (2*n)) vertical) :=
  fixedEquiv (wordEquivTiling n) vWord (vertical • ·) word_vertical

noncomputable def halfTurnWordEquiv (n : ℕ) :
    {W : Word n // rWord W = W} ≃ ↥(MulAction.fixedBy (Tiling 3 (2*n)) halfTurn) :=
  fixedEquiv (wordEquivTiling n) rWord (halfTurn • ·) word_halfTurn

theorem horizontal_fixed_word {n : ℕ} (W : Word n) :
    horizontal • wordEquivTiling n W = wordEquivTiling n W ↔ W.val.map flip = W.val := by
  rw [word_horizontal,(wordEquivTiling n).injective.eq_iff,Subtype.ext_iff]
  rfl

theorem vertical_fixed_word {n : ℕ} (W : Word n) :
    vertical • wordEquivTiling n W = wordEquivTiling n W ↔ W.val.reverse = W.val := by
  rw [word_vertical,(wordEquivTiling n).injective.eq_iff,Subtype.ext_iff]
  rfl

theorem halfTurn_fixed_word {n : ℕ} (W : Word n) :
    halfTurn • wordEquivTiling n W = wordEquivTiling n W ↔ W.val.reverse.map flip = W.val := by
  rw [word_halfTurn,(wordEquivTiling n).injective.eq_iff,Subtype.ext_iff]
  rfl

end Domino.Blocks
