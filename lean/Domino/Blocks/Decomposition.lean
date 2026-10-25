module

public import Domino.Blocks.Letters

/-! 首次回空分类与唯一字分解，直接从全部局部转移出发。 -/

@[expose] public section
namespace Domino.Blocks

def Valid (p : State 3) : List (State 3) → Prop
  | [] => p = ∅
  | q :: L => Legal3 p q ∧ Valid q L

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem transition_table :
    (∀ q, Legal3 ∅ q ↔ q = Finset.univ ∨ q = single false ∨ q = single true) ∧
    (∀ q, Legal3 Finset.univ q ↔ q = ∅) ∧
    (∀ b q, Legal3 (single b) q ↔ q = ∅ ∨ q = paired b) ∧
    (∀ b q, Legal3 (paired b) q ↔ q = single b) := by decide

theorem valid_arm (b : Bool) (k : ℕ) (L : List (State 3)) (h : Valid ∅ L) :
    Valid ∅ (core (.arm b k) ++ ∅ :: L) ∧ Valid (paired b) (core (.arm b k) ++ ∅ :: L) := by
  induction k with
  | zero =>
    simp only [core, List.cons_append, List.nil_append, Valid]
    have h0 : Legal3 ∅ (single b) := (transition_table.1 _).mpr (by cases b <;> simp)
    have h1 : Legal3 (single b) ∅ := (transition_table.2.2.1 _ _).mpr (Or.inl rfl)
    have h2 : Legal3 (paired b) (single b) := (transition_table.2.2.2 _ _).mpr rfl
    exact ⟨⟨h0,h1,h⟩, ⟨h2,h1,h⟩⟩
  | succ k ih =>
    simp only [core, List.cons_append, Valid]
    have h0 : Legal3 ∅ (single b) := (transition_table.1 _).mpr (by cases b <;> simp)
    have h1 : Legal3 (single b) (paired b) := (transition_table.2.2.1 _ _).mpr (Or.inr rfl)
    have h2 : Legal3 (paired b) (single b) := (transition_table.2.2.2 _ _).mpr rfl
    exact ⟨⟨h0,h1,ih.2⟩,⟨h2,h1,ih.2⟩⟩

theorem valid_trace (W : List Letter) : Valid ∅ (trace W) := by
  induction W with
  | nil => rfl
  | cons a W ih =>
    rw [trace_cons]
    cases a with
    | c =>
      simp only [core, List.cons_append, List.nil_append, Valid]
      exact ⟨(transition_table.1 _).mpr (Or.inl rfl), (transition_table.2.1 _).mpr rfl, ih⟩
    | arm b k => exact (valid_arm b k _ ih).1

theorem valid_complete_aux (L : List (State 3)) :
    (Valid ∅ L → ∃ W, trace W = L) ∧
    (∀ b, Valid (paired b) L → ∃ k W, trace (.arm b k :: W) = L) := by
  induction L using List.twoStepInduction with
  | nil => exact ⟨fun _ => ⟨[],rfl⟩, fun b h => (paired_ne_empty b h).elim⟩
  | singleton q =>
    constructor
    · rintro ⟨h,hq⟩
      change q = ∅ at hq
      subst q
      have : ¬ Legal3 ∅ ∅ := by decide
      exact (this h).elim
    · intro b h
      rcases h with ⟨h,hq⟩
      change q = ∅ at hq
      have he := (transition_table.2.2.2 b q).mp h
      exact (single_ne_empty b (he.symm.trans hq)).elim
  | cons_cons q r L ih _ =>
    have arm_case (b : Bool) (h : Valid (single b) (r :: L)) :
        ∃ k W, trace (.arm b k :: W) = single b :: r :: L := by
      rcases (transition_table.2.2.1 b r).mp h.1 with hr | hr
      · subst r
        obtain ⟨W,hW⟩ := ih.1 h.2
        exact ⟨0,W,by simp [trace_cons, core, hW]⟩
      · subst r
        obtain ⟨k,W,hW⟩ := ih.2 b h.2
        refine ⟨k+1,W,?_⟩
        simpa only [trace_cons, core, List.cons_append] using congrArg (fun L => single b :: paired b :: L) hW
    constructor
    · intro h
      rcases (transition_table.1 q).mp h.1 with hq | hq | hq
      · subst q
        have hr := (transition_table.2.1 r).mp h.2.1
        subst r
        obtain ⟨W,hW⟩ := ih.1 h.2.2
        exact ⟨.c :: W,by simp [trace_cons, core, hW]⟩
      · subst q
        obtain ⟨k,W,hW⟩ := arm_case false h.2
        exact ⟨.arm false k :: W,hW⟩
      · subst q
        obtain ⟨k,W,hW⟩ := arm_case true h.2
        exact ⟨.arm true k :: W,hW⟩
    · intro b h
      have hq := (transition_table.2.2.2 b q).mp h.1
      subst q
      exact arm_case b h.2

theorem unique_decomposition (L : List (State 3)) (h : Valid ∅ L) :
    ∃! W, trace W = L := by
  obtain ⟨W,hW⟩ := (valid_complete_aux L).1 h
  exact ⟨W,hW,fun V hV => trace_injective (hV.trans hW.symm)⟩

theorem valid_decode (L : List (State 3)) (h : Valid ∅ L) : trace (decode L) = L := by
  obtain ⟨W,rfl⟩ := (valid_complete_aux L).1 h
  simp

def Irreducible (L : List (State 3)) : Prop :=
  L ≠ [] ∧ Valid ∅ L ∧ ∅ ∉ L.dropLast

theorem irreducible_letter (a : Letter) : Irreducible (trace [a]) := by
  refine ⟨?_,valid_trace [a],?_⟩
  · have h := trace_length [a]; have := weight_pos a
    intro he; simp [he] at h; omega
  · simpa [trace_cons] using empty_not_mem_core a

theorem irreducible_iff_letter (L : List (State 3)) :
    Irreducible L ↔ ∃! a, trace [a] = L := by
  constructor
  · rintro ⟨hne,hv,hi⟩
    obtain ⟨W,hW⟩ := (valid_complete_aux L).1 hv
    cases W with
    | nil => exact (hne hW.symm).elim
    | cons a W =>
      cases W with
      | nil => exact ⟨a,hW,fun b hb => by have := trace_injective (hb.trans hW.symm); simpa using this⟩
      | cons b W =>
        have he : (∅ : State 3) ∈ (trace (a :: b :: W)).dropLast := by
          have hb : trace (b :: W) ≠ [] := by
            intro hh
            have := trace_length (b :: W)
            have := weight_pos b
            simp [hh] at *; omega
          simp only [trace_cons] at hb ⊢
          rw [List.dropLast_append_of_ne_nil (by simp)]
          have hc : (core b ++ ∅ :: trace W) ≠ [] := hb
          rw [List.dropLast_cons_of_ne_nil hc]
          simp
        exact (hi (hW ▸ he)).elim
  · rintro ⟨a,ha,_⟩
    rw [← ha]
    exact irreducible_letter a

end Domino.Blocks
