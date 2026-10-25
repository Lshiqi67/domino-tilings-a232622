module

public import Domino.Blocks.Graded
public import Domino.ThreeRows.Algebra

/-! A05：从字首分解及基本块基数推导普通生成函数，不使用半棋盘递推。 -/

@[expose] public section
namespace Domino.Blocks
open PowerSeries

instance letterGradeFinite (n : ℕ) : Finite (Grade weight n) := by
  apply Finite.of_injective (fun a : Grade weight n => (⟨[a.val], by simpa [mass] using a.property⟩ : Word n))
  intro a b h
  apply Subtype.ext
  exact (List.cons.inj (congrArg Subtype.val h)).1

noncomputable instance letterGradeFintype (n : ℕ) : Fintype (Grade weight n) := Fintype.ofFinite _

def letterSuccEquiv (n : ℕ) : Grade weight (n+1) ≃ {_u : Unit // n=0} ⊕ Bool where
  toFun a := match a with
    | ⟨.c,h⟩ => .inl ⟨(),by change 1=n+1 at h; omega⟩
    | ⟨.arm b _,_⟩ => .inr b
  invFun x := match x with
    | .inl u => ⟨.c,by change 1=n+1; rw [u.property]⟩
    | .inr b => ⟨.arm b n,rfl⟩
  left_inv a := by
    rcases a with ⟨a,h⟩
    cases a with
    | c => rfl
    | arm b k =>
      have : k=n := by change k+1=n+1 at h; omega
      subst k
      rfl
  right_inv x := by rcases x with ⟨⟨⟩,h⟩ | b <;> rfl

@[simp] theorem letter_card_zero : Fintype.card (Grade weight 0) = 0 := by
  let : IsEmpty (Grade weight 0) := ⟨fun a => (Nat.ne_of_gt (weight_pos a.val)) a.property⟩
  exact Fintype.card_eq_zero

@[simp] theorem letter_card_succ (n : ℕ) : Fintype.card (Grade weight (n+1)) = if n=0 then 3 else 2 := by
  have h := Fintype.card_congr (letterSuccEquiv n)
  simp only [Fintype.card_sum,unit_grade_card,Fintype.card_bool] at h
  by_cases hn : n=0 <;> simpa [hn] using h

noncomputable def letterSeries : PowerSeries ℚ := gradedSeries weight
noncomputable def wordSeries : PowerSeries ℚ := gradedSeries mass

@[simp] theorem letter_coeff_zero : coeff 0 letterSeries = 0 := by simp [letterSeries]
@[simp] theorem letter_coeff_one : coeff 1 letterSeries = 3 := by simp [letterSeries]
@[simp] theorem letter_coeff_large (n : ℕ) : coeff (n+2) letterSeries = 2 := by
  simp [letterSeries,show n+2=(n+1)+1 by omega]

@[simp] theorem letter_constant : constantCoeff letterSeries = 0 := by
  simpa only [coeff_zero_eq_constantCoeff] using letter_coeff_zero

theorem letter_series_identity : (1-X) * letterSeries = 3*X-X^2 := by
  ext n
  rcases n with _ | _ | n
  · simp [sub_mul]
  · simp [sub_mul,coeff_succ_X_mul]
  · by_cases hn : n=0
    · subst n; norm_num [sub_mul,coeff_succ_X_mul,coeff_X]
    · simp [sub_mul,coeff_succ_X_mul,letterSeries,hn,coeff_X]

def wordHeadEquiv (n : ℕ) : Word n ≃ {_u : Unit // n=0} ⊕ Grade (fun p : Letter × List Letter => weight p.1 + mass p.2) n where
  toFun W := match W with
    | ⟨[],h⟩ => .inl ⟨(),h.symm⟩
    | ⟨a::W,h⟩ => .inr ⟨(a,W),h⟩
  invFun x := match x with
    | .inl u => ⟨[],u.property.symm⟩
    | .inr p => ⟨p.val.1 :: p.val.2,p.property⟩
  left_inv W := by rcases W with ⟨_|⟨a,W⟩,h⟩ <;> rfl
  right_inv x := by rcases x with ⟨⟨⟩,h⟩ | ⟨⟨a,W⟩,h⟩ <;> rfl

theorem word_series_equation : wordSeries = 1 + letterSeries * wordSeries := by
  rw [show letterSeries * wordSeries = gradedSeries (fun p : Letter × List Letter => weight p.1 + mass p.2) from (graded_product weight mass).symm]
  ext n
  simp only [wordSeries,coeff_gradedSeries,map_add,coeff_one]
  have h := Fintype.card_congr (wordHeadEquiv n)
  simp only [Fintype.card_sum,unit_grade_card] at h
  by_cases hn : n=0 <;> simp [hn] at * <;> exact_mod_cast h

theorem word_series_inverse : (1-letterSeries) * wordSeries = 1 := by
  linear_combination word_series_equation

theorem word_ordinary_identity : ordinaryDenom * wordSeries = 1-X := by
  have hden : (1-X)*(1-letterSeries)=ordinaryDenom := by
    have h := letter_series_identity
    unfold ordinaryDenom
    linear_combination -h
  rw [← hden,mul_assoc,word_series_inverse,mul_one]

theorem wordSeries_actual : wordSeries = countSeries (ordinaryCount 3) := by
  ext n
  simp [wordSeries]

end Domino.Blocks
