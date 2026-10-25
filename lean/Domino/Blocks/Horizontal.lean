module

public import Domino.Blocks.FixedSeries

/-! A06：上下反射固定字只含 C，故每个半宽恰有一个。 -/

@[expose] public section
namespace Domino.Blocks
open PowerSeries

theorem mass_replicate_c (n : ℕ) : mass (List.replicate n Letter.c) = n := by simp [mass,weight]

theorem fixed_letters_iff (W : List Letter) : W.map flip = W ↔ W = List.replicate (mass W) Letter.c := by
  constructor
  · intro h
    induction W with
    | nil => rfl
    | cons a W ih =>
      have he := (List.cons.inj h).1
      have hw := (List.cons.inj h).2
      have ha := (flip_eq_iff a).mp he
      subst a
      rw [ih hw]
      simp only [mass_cons,weight,mass_replicate_c]
      rw [Nat.add_comm 1,List.replicate_succ]
  · intro h
    rw [h]
    simp [flip]

def horizontalDefault (n : ℕ) : {W : Word n // hWord W = W} :=
  ⟨⟨List.replicate n .c,mass_replicate_c n⟩,by apply Subtype.ext; simp [hWord,flip]⟩

theorem horizontalWord_unique (n : ℕ) (W : {W : Word n // hWord W = W}) : W = horizontalDefault n := by
  apply Subtype.ext
  apply Subtype.ext
  have h : W.val.val.map flip = W.val.val := congrArg Subtype.val W.property
  have he := (fixed_letters_iff W.val.val).mp h
  simpa [W.val.property,horizontalDefault] using he

theorem horizontal_card_via_words (n : ℕ) : fixedCount 3 n horizontal = 1 := by
  classical
  let : Unique {W : Word n // hWord W = W} := ⟨⟨horizontalDefault n⟩,horizontalWord_unique n⟩
  calc
    fixedCount 3 n horizontal = Fintype.card {W : Word n // hWord W = W} :=
      Fintype.card_congr (horizontalWordEquiv n).symm
    _ = 1 := Fintype.card_unique

theorem horizontal_series_via_words :
    (1-X) * countSeries (fun n => fixedCount 3 n horizontal) = 1 := by
  ext n
  cases n with
  | zero => simp [sub_mul,countSeries,horizontal_card_via_words]
  | succ n => simp [sub_mul,coeff_succ_X_mul,horizontal_card_via_words,coeff_one]

end Domino.Blocks
