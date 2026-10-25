module

public import Domino.Blocks.Symmetry

/-! A07/A08：普通和带对合回文的唯一半字、可选中心分解。 -/

@[expose] public section
namespace Domino.Blocks

def twist (b : Bool) (a : Letter) : Letter := if b then flip a else a
def mirror (b : Bool) (W : List Letter) : List Letter := W.reverse.map (twist b)
def centerMass (c : Option Letter) : ℕ := (c.toList.map weight).sum
def CenterOK (b : Bool) (c : Option Letter) : Prop := c.toList.map (twist b) = c.toList
def assemble (b : Bool) (U : List Letter) (c : Option Letter) : List Letter :=
  U ++ c.toList ++ mirror b U

@[simp] theorem twist_twice (b : Bool) (a : Letter) : twist b (twist b a) = a := by cases b <;> simp [twist]
@[simp] theorem weight_twist (b : Bool) (a : Letter) : weight (twist b a) = weight a := by cases b <;> simp [twist]
@[simp] theorem mirror_nil (b : Bool) : mirror b [] = [] := rfl
@[simp] theorem mirror_cons (b : Bool) (a : Letter) (U : List Letter) :
    mirror b (a :: U) = mirror b U ++ [twist b a] := by simp [mirror]
@[simp] theorem mirror_append (b : Bool) (U V : List Letter) :
    mirror b (U ++ V) = mirror b V ++ mirror b U := by simp [mirror]
@[simp] theorem mirror_twice (b : Bool) (W : List Letter) : mirror b (mirror b W) = W := by
  simp [mirror,List.map_reverse,List.map_map,Function.comp_def]
@[simp] theorem mass_mirror (b : Bool) (W : List Letter) : mass (mirror b W) = mass W := by
  simp [mass,mirror,List.map_reverse,List.map_map,Function.comp_def]
@[simp] theorem length_mirror (b : Bool) (W : List Letter) : (mirror b W).length = W.length := by simp [mirror]
@[simp] theorem mass_assemble (b : Bool) (U : List Letter) (c : Option Letter) :
    mass (assemble b U c) = 2 * mass U + centerMass c := by
  simp only [assemble,mass_append,mass_mirror]
  change mass U + centerMass c + mass U = _
  omega

@[simp] theorem center_none (b : Bool) : CenterOK b none := rfl
@[simp] theorem center_some (b : Bool) (a : Letter) : CenterOK b (some a) ↔ twist b a = a := by simp [CenterOK]
@[simp] theorem center_false (c : Option Letter) : CenterOK false c := by cases c <;> simp [CenterOK,twist]

theorem assemble_fixed (b : Bool) (U : List Letter) (c : Option Letter) (hc : CenterOK b c) :
    mirror b (assemble b U c) = assemble b U c := by
  have h : mirror b c.toList = c.toList := by
    cases c with
    | none => rfl
    | some a => simpa [CenterOK,mirror] using hc
  simp [assemble,mirror_append,h,List.append_assoc]

theorem palindrome_exists (b : Bool) (W : List Letter) (h : mirror b W = W) :
    ∃ U c, CenterOK b c ∧ assemble b U c = W := by
  induction W using List.bidirectionalRec with
  | nil => exact ⟨[],none,rfl,rfl⟩
  | singleton a =>
    refine ⟨[],some a,?_,rfl⟩
    simpa [CenterOK,mirror] using h
  | cons_append a L z ih =>
    have hh : twist b z :: (mirror b L ++ [twist b a]) = a :: (L ++ [z]) := by
      simpa only [mirror_cons,mirror_append,mirror_nil,List.nil_append,List.cons_append] using h
    have hza : twist b z = a := (List.cons.inj hh).1
    have haz : twist b a = z := by rw [← hza,twist_twice]
    have hm : mirror b L = L := by
      have ht := (List.cons.inj hh).2
      rw [haz] at ht
      exact List.append_cancel_right ht
    obtain ⟨U,c,hc,he⟩ := ih hm
    refine ⟨a::U,c,hc,?_⟩
    simpa only [assemble,mirror_cons,List.cons_append,List.append_assoc,haz] using congrArg (fun L => a :: (L ++ [z])) he

theorem assemble_injective (b : Bool) :
    Function.Injective (fun p : List Letter × Option Letter => assemble b p.1 p.2) := by
  rintro ⟨U,c⟩ ⟨V,d⟩ h
  have hl := congrArg List.length h
  simp only [assemble,List.length_append,length_mirror] at hl
  have hc : c.toList.length ≤ 1 := by cases c <;> simp
  have hd : d.toList.length ≤ 1 := by cases d <;> simp
  have huv : U.length = V.length := by omega
  have ht := congrArg (List.take U.length) h
  have he : U = V := by simpa [assemble,List.take_append,huv] using ht
  subst V
  have hc : c.toList = d.toList := by simpa [assemble,List.append_assoc] using h
  have hcd : c = d := by cases c <;> cases d <;> simp_all
  subst d
  rfl

theorem palindrome_unique (b : Bool) (W : List Letter) (h : mirror b W = W) :
    ∃! p : List Letter × Option Letter, CenterOK b p.2 ∧ assemble b p.1 p.2 = W := by
  obtain ⟨U,c,hc,he⟩ := palindrome_exists b W h
  exact ⟨(U,c),⟨hc,he⟩,fun p hp => assemble_injective b (hp.2.trans he.symm)⟩

abbrev Center (b : Bool) := {c : Option Letter // CenterOK b c}
abbrev HalfData (b : Bool) (n : ℕ) :=
  {p : List Letter × Center b // 2 * mass p.1 + centerMass p.2.val = n}
abbrev PalWord (b : Bool) (n : ℕ) := {W : Word n // mirror b W.val = W.val}

def assembleHalf {b : Bool} {n : ℕ} (p : HalfData b n) : PalWord b n :=
  ⟨⟨assemble b p.val.1 p.val.2.val, by simpa using p.property⟩, assemble_fixed b _ _ p.val.2.property⟩

theorem assembleHalf_bijective (b : Bool) (n : ℕ) : Function.Bijective (@assembleHalf b n) := by
  constructor
  · intro p q h
    have he : (p.val.1,p.val.2.val) = (q.val.1,q.val.2.val) :=
      assemble_injective b (show assemble b p.val.1 p.val.2.val = assemble b q.val.1 q.val.2.val from
        congrArg (fun W : PalWord b n => W.val.val) h)
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x : List Letter × Option Letter => x.1) he
    · exact Subtype.ext (congrArg (fun x : List Letter × Option Letter => x.2) he)
  · intro W
    obtain ⟨U,c,hc,he⟩ := palindrome_exists b W.val.val W.property
    refine ⟨⟨(U,⟨c,hc⟩),?_⟩,?_⟩
    · rw [← mass_assemble b U c,he]; exact W.val.property
    · apply Subtype.ext; apply Subtype.ext; exact he

noncomputable def palindromeEquiv (b : Bool) (n : ℕ) : HalfData b n ≃ PalWord b n :=
  Equiv.ofBijective assembleHalf (assembleHalf_bijective b n)

noncomputable instance palWordFintype (b : Bool) (n : ℕ) : Fintype (PalWord b n) := Fintype.ofFinite _
instance halfDataFinite (b : Bool) (n : ℕ) : Finite (HalfData b n) :=
  Finite.of_equiv _ (palindromeEquiv b n).symm

end Domino.Blocks
