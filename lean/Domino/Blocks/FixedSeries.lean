module

public import Domino.Blocks.Palindromes
public import Domino.Blocks.WordSeries

/-! 回文半字加倍权重与中心类型的有限基数生成函数。 -/

@[expose] public section
namespace Domino.Blocks
open PowerSeries

instance doubleMassFinite (n : ℕ) : Finite (Grade (fun W => 2*mass W) n) := by
  apply Finite.of_injective (fun W : Grade (fun W => 2*mass W) n =>
    (⟨W.val,by have := W.property; dsimp at *; omega⟩ : Word (n/2)))
  intro U V h
  exact Subtype.ext (congrArg (fun W : Word (n/2) => W.val) h)
noncomputable instance doubleMassFintype (n : ℕ) : Fintype (Grade (fun W => 2*mass W) n) := Fintype.ofFinite _

def doubleMassEquiv (n : ℕ) : Grade (fun W => 2*mass W) (2*n) ≃ Word n where
  toFun W := ⟨W.val,by have := W.property; dsimp at *; omega⟩
  invFun W := ⟨W.val,by simp [W.property]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem double_mass_series : gradedSeries (fun W => 2*mass W) = doubleSeries wordSeries := by
  apply series_ext_parity
  · intro n
    rw [coeff_gradedSeries,coeff_doubleSeries_even]
    simp only [wordSeries,coeff_gradedSeries]
    change (Fintype.card (Grade (fun W => 2*mass W) (2*n)) : ℚ) = (Fintype.card (Word n) : ℚ)
    exact_mod_cast Fintype.card_congr (doubleMassEquiv n)
  · intro n
    let : IsEmpty (Grade (fun W => 2*mass W) (2*n+1)) := ⟨fun W => by have := W.property; dsimp at *; omega⟩
    simp

instance centerGradeFinite (b : Bool) (n : ℕ) : Finite (Grade (fun c : Center b => centerMass c.val) n) := by
  apply Finite.of_injective (fun c : Grade (fun c : Center b => centerMass c.val) n =>
    (⟨c.val.val,c.property⟩ : Grade (optionMass weight) n))
  intro c d h
  exact Subtype.ext (Subtype.ext (congrArg (fun c : Grade (optionMass weight) n => c.val) h))
noncomputable instance centerGradeFintype (b : Bool) (n : ℕ) : Fintype (Grade (fun c : Center b => centerMass c.val) n) := Fintype.ofFinite _

noncomputable def centerSeries (b : Bool) : PowerSeries ℚ := gradedSeries (fun c : Center b => centerMass c.val)

def centerFalseGradeEquiv (n : ℕ) : Grade (fun c : Center false => centerMass c.val) n ≃ Grade (optionMass weight) n where
  toFun c := ⟨c.val.val,c.property⟩
  invFun c := ⟨⟨c.val,center_false _⟩,c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem center_series_false : centerSeries false = 1 + letterSeries := by
  change centerSeries false = 1 + gradedSeries weight
  rw [← graded_option weight]
  ext n
  simp only [centerSeries,coeff_gradedSeries]
  exact_mod_cast Fintype.card_congr (centerFalseGradeEquiv n)

theorem flip_eq_iff (a : Letter) : flip a = a ↔ a = .c := by
  cases a with
  | c => simp [flip]
  | arm b k => cases b <;> simp [flip]

theorem center_true_cases (c : Center true) : c.val = none ∨ c.val = some Letter.c := by
  rcases c with ⟨_|a,h⟩
  · exact Or.inl rfl
  · have ha : a=Letter.c := (flip_eq_iff a).mp (by simpa [CenterOK,twist] using h)
    exact Or.inr (congrArg some ha)

def centerTrueEquiv : Center true ≃ Fin 2 where
  toFun c := match c.val with | none => 0 | some _ => 1
  invFun i := if i=0 then ⟨none,center_none _⟩ else ⟨some .c,by simp [CenterOK,twist,flip]⟩
  left_inv c := by
    rcases center_true_cases c with h | h
    · apply Subtype.ext; simp [h]
    · apply Subtype.ext; simp [h]
  right_inv i := by fin_cases i <;> rfl

theorem center_true_mass (c : Center true) : centerMass c.val = (centerTrueEquiv c).val := by
  rcases center_true_cases c with h | h <;> simp [centerMass,centerTrueEquiv,h,weight]

def centerTrueGradeEquiv (n : ℕ) : Grade (fun c : Center true => centerMass c.val) n ≃ {i : Fin 2 // i.val=n} where
  toFun c := ⟨centerTrueEquiv c.val,by rw [← center_true_mass]; exact c.property⟩
  invFun i := ⟨centerTrueEquiv.symm i.val,by dsimp; rw [center_true_mass,centerTrueEquiv.apply_symm_apply]; exact i.property⟩
  left_inv c := Subtype.ext (centerTrueEquiv.symm_apply_apply c.val)
  right_inv i := Subtype.ext (centerTrueEquiv.apply_symm_apply i.val)

theorem center_series_true : centerSeries true = 1+X := by
  ext n
  have h := Fintype.card_congr (centerTrueGradeEquiv n)
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter] at h
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,zero_add,add_zero] at h
  simp only [centerSeries,coeff_gradedSeries,map_add,coeff_one,coeff_X]
  simp only [eq_comm] at h
  exact_mod_cast h.symm

noncomputable def palSeries (b : Bool) : PowerSeries ℚ := countSeries fun n => Fintype.card (PalWord b n)

theorem palindrome_series (b : Bool) : palSeries b = doubleSeries wordSeries * centerSeries b := by
  rw [← double_mass_series, centerSeries, ← graded_product]
  ext n
  let : Fintype (HalfData b n) := pairGradeFintype (fun W => 2*mass W) (fun c : Center b => centerMass c.val) n
  simp only [palSeries,coeff_countSeries,coeff_gradedSeries]
  exact_mod_cast (Fintype.card_congr (palindromeEquiv b n)).symm

noncomputable def palWordFixedEquiv (b : Bool) (n : ℕ) :
    PalWord b n ≃ ↥(MulAction.fixedBy (Tiling 3 (2*n)) (axialSymmetry b)) := by
  cases b
  · exact (Equiv.subtypeEquivRight (fun W : Word n => by simp [mirror,show twist false = id by funext a; rfl,vWord,Subtype.ext_iff])).trans (verticalWordEquiv n)
  · exact (Equiv.subtypeEquivRight (fun W : Word n => by simp [mirror,show twist true = flip by funext a; rfl,rWord,hWord,vWord,Subtype.ext_iff])).trans (halfTurnWordEquiv n)

theorem palSeries_actual (b : Bool) : palSeries b = countSeries (fun n => fixedCount 3 n (axialSymmetry b)) := by
  classical
  ext n
  simp only [palSeries,coeff_countSeries]
  have he : Fintype.card ↥(MulAction.fixedBy (Tiling 3 (2*n)) (axialSymmetry b)) = fixedCount 3 n (axialSymmetry b) := Fintype.card_congr (Equiv.refl _)
  exact_mod_cast (Fintype.card_congr (palWordFixedEquiv b n)).trans he

theorem vertical_word_series : countSeries (fun n => fixedCount 3 n vertical) = (1+letterSeries)*doubleSeries wordSeries := by
  change countSeries (fun n => fixedCount 3 n (axialSymmetry false)) = _
  rw [← palSeries_actual false,palindrome_series,center_series_false,mul_comm]

theorem halfTurn_word_series : countSeries (fun n => fixedCount 3 n halfTurn) = (1+X)*doubleSeries wordSeries := by
  change countSeries (fun n => fixedCount 3 n (axialSymmetry true)) = _
  rw [← palSeries_actual true,palindrome_series,center_series_true,mul_comm]

end Domino.Blocks
