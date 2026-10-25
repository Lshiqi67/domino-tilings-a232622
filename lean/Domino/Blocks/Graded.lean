module

public import Domino.Blocks.Geometry
public import Domino.Series.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! 非负整数分级有限对象的 Cauchy 乘积。所有计数是实际有限纤维基数。 -/

@[expose] public section
namespace Domino.Blocks
open PowerSeries

abbrev Grade {α : Type*} (f : α → ℕ) (n : ℕ) := {a // f a = n}

noncomputable def gradedSeries {α : Type*} (f : α → ℕ) [∀ n, Fintype (Grade f n)] : PowerSeries ℚ :=
  countSeries fun n => Fintype.card (Grade f n)

@[simp] theorem coeff_gradedSeries {α : Type*} (f : α → ℕ) [∀ n, Fintype (Grade f n)] (n : ℕ) :
    coeff n (gradedSeries f) = (Fintype.card (Grade f n) : ℚ) := coeff_countSeries _ n

def pairGradeEquiv {α β : Type*} (f : α → ℕ) (g : β → ℕ) (n : ℕ) :
    Grade (fun p : α × β => f p.1 + g p.2) n ≃
      Σ i : Fin (n+1), Grade f i.val × Grade g (n-i.val) where
  toFun p := ⟨⟨f p.val.1, by have := p.property; dsimp at *; omega⟩,
    ⟨p.val.1,rfl⟩,⟨p.val.2,by have := p.property; dsimp at *; omega⟩⟩
  invFun p := ⟨(p.2.1.val,p.2.2.val),by have := p.2.1.property; have := p.2.2.property; have := p.1.isLt; dsimp at *; omega⟩
  left_inv p := by cases p; rfl
  right_inv p := by
    rcases p with ⟨⟨i,hi⟩,⟨a,ha⟩,⟨b,hb⟩⟩
    dsimp at ha
    subst i
    rfl

noncomputable instance pairGradeFintype {α β : Type*} (f : α → ℕ) (g : β → ℕ)
    [∀ n, Fintype (Grade f n)] [∀ n, Fintype (Grade g n)] (n : ℕ) :
    Fintype (Grade (fun p : α × β => f p.1 + g p.2) n) :=
  Fintype.ofEquiv _ (pairGradeEquiv f g n).symm

theorem graded_product {α β : Type*} (f : α → ℕ) (g : β → ℕ)
    [∀ n, Fintype (Grade f n)] [∀ n, Fintype (Grade g n)] :
    gradedSeries (fun p : α × β => f p.1 + g p.2) = gradedSeries f * gradedSeries g := by
  ext n
  rw [coeff_gradedSeries,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_gradedSeries]
  have h := Fintype.card_congr (pairGradeEquiv f g n)
  simp only [Fintype.card_sigma,Fintype.card_prod] at h
  have hs := Fin.sum_univ_eq_sum_range (fun i => Fintype.card (Grade f i) * Fintype.card (Grade g (n-i))) (n+1)
  rw [hs] at h
  exact_mod_cast h

def optionMass {α : Type*} (f : α → ℕ) (o : Option α) : ℕ := (o.toList.map f).sum

def optionGradeEquiv {α : Type*} (f : α → ℕ) (n : ℕ) :
    Grade (optionMass f) n ≃ {_u : Unit // n=0} ⊕ Grade f n where
  toFun o := match o with
    | ⟨none,h⟩ => .inl ⟨(),h.symm⟩
    | ⟨some a,h⟩ => .inr ⟨a,by simpa [optionMass] using h⟩
  invFun x := match x with
    | .inl u => ⟨none,u.property.symm⟩
    | .inr a => ⟨some a.val,by simpa [optionMass] using a.property⟩
  left_inv o := by rcases o with ⟨_|a,h⟩ <;> rfl
  right_inv x := by rcases x with ⟨⟨⟩,h⟩ | ⟨a,h⟩ <;> rfl

noncomputable instance optionGradeFintype {α : Type*} (f : α → ℕ)
    [∀ n, Fintype (Grade f n)] (n : ℕ) : Fintype (Grade (optionMass f) n) :=
  Fintype.ofEquiv _ (optionGradeEquiv f n).symm

theorem unit_grade_card (n : ℕ) : Fintype.card {_u : Unit // n=0} = if n=0 then 1 else 0 := by
  by_cases h : n=0 <;> simp [h]

theorem graded_option {α : Type*} (f : α → ℕ) [∀ n, Fintype (Grade f n)] :
    gradedSeries (optionMass f) = 1 + gradedSeries f := by
  ext n
  simp only [coeff_gradedSeries,map_add,coeff_one]
  have h := Fintype.card_congr (optionGradeEquiv f n)
  simp only [Fintype.card_sum,unit_grade_card] at h
  by_cases hn : n=0 <;> simp [hn] at * <;> exact_mod_cast h

end Domino.Blocks
