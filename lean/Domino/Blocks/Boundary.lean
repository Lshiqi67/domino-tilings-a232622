module

public import Domino.Blocks.WordSeries

/-! 基本块与几何断口的对应及 k=1 边界。 -/

@[expose] public section
namespace Domino.Blocks

theorem no_internal_empty_iff (L : List (State 3)) :
    (∅ : State 3) ∉ L.dropLast ↔
      ∀ k, 0<k → k<L.length → (∅ :: L).getD k ∅ ≠ ∅ := by
  constructor
  · intro h k hk hkw he
    cases k with
    | zero => omega
    | succ k =>
      apply h
      have hk' : k < L.dropLast.length := by simp; omega
      apply List.mem_iff_getElem.mpr
      refine ⟨k,hk',?_⟩
      change L.getD k ∅ = ∅ at he
      rw [List.getD_eq_getElem L ∅ (by omega)] at he
      simpa only [List.getElem_dropLast] using he
  · intro h he
    obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp he
    have hkl : k+1<L.length := by simp only [List.length_dropLast] at hk; omega
    apply h (k+1) (by omega) hkl
    change L.getD k ∅ = ∅
    rw [List.getD_eq_getElem L ∅ (by omega)]
    simpa only [List.getElem_dropLast] using he

def BasicTiling {w : ℕ} (T : Tiling 3 w) : Prop :=
  0<w ∧ ∀ k, 0<k → k<w → (tilingPath T).state k ≠ ∅

theorem basic_iff_irreducible {w : ℕ} (T : Tiling 3 w) :
    BasicTiling T ↔ Irreducible (pathList (tilingPath T)) := by
  unfold BasicTiling Irreducible
  rw [no_internal_empty_iff,pathList_length]
  simp only [pathList_getD]
  have hn : pathList (tilingPath T) ≠ [] ↔ 0<w := by rw [← List.length_pos_iff,pathList_length]
  rw [hn]
  exact ⟨fun h => ⟨h.1,pathList_valid _,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩

theorem empty_cut_iff_no_crossing {w : ℕ} (T : Tiling 3 w) (k : ℕ) (hk : 0<k) (hkw : k<w) :
    (tilingPath T).state k = ∅ ↔
      ∀ r : Fin 3, ((r,⟨k-1,by omega⟩),(r,⟨k,hkw⟩)) ∉ coverBonds T := by
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [tilingPath_cut T k hk hkw]

theorem word_pathList {n : ℕ} (W : Word n) : pathList (tilingPath (wordEquivTiling n W)) = trace W.val := by
  change pathList ((tilingEquivClosedPath (2*n)) ((tilingEquivClosedPath (2*n)).symm (wordPath W))) = _
  rw [(tilingEquivClosedPath (2*n)).apply_symm_apply]
  exact pathList_pathOfList _ _ _ _

theorem basic_word_iff {n : ℕ} (W : Word n) :
    BasicTiling (wordEquivTiling n W) ↔ ∃ a, W.val = [a] := by
  rw [basic_iff_irreducible,word_pathList,irreducible_iff_letter]
  constructor
  · rintro ⟨a,ha,_⟩
    exact ⟨a,(trace_injective ha).symm⟩
  · rintro ⟨a,ha⟩
    refine ⟨a,by rw [ha],?_⟩
    intro b hb
    have h := trace_injective (hb.trans (congrArg trace ha))
    simpa using h

def letterToWord {n : ℕ} (a : Grade weight n) : Word n := ⟨[a.val],by simpa [mass] using a.property⟩

noncomputable def letterToBasic {n : ℕ} (a : Grade weight n) : {T : Tiling 3 (2*n) // BasicTiling T} :=
  ⟨wordEquivTiling n (letterToWord a),(basic_word_iff _).mpr ⟨a.val,rfl⟩⟩

theorem letterToBasic_bijective (n : ℕ) : Function.Bijective (@letterToBasic n) := by
  constructor
  · intro a b h
    have he := (wordEquivTiling n).injective (congrArg Subtype.val h)
    exact Subtype.ext (List.cons.inj (congrArg (fun W : Word n => W.val) he)).1
  · intro T
    let W := (wordEquivTiling n).symm T.val
    have hb : BasicTiling (wordEquivTiling n W) := by simpa [W] using T.property
    obtain ⟨a,ha⟩ := (basic_word_iff W).mp hb
    have hw : weight a=n := by have := W.property; rw [ha] at this; simpa [mass] using this
    refine ⟨⟨a,hw⟩,?_⟩
    apply Subtype.ext
    change wordEquivTiling n (letterToWord ⟨a,hw⟩) = T.val
    have he : letterToWord ⟨a,hw⟩ = W := Subtype.ext ha.symm
    rw [he]
    exact (wordEquivTiling n).apply_symm_apply T.val

noncomputable def letterEquivBasic (n : ℕ) : Grade weight n ≃ {T : Tiling 3 (2*n) // BasicTiling T} :=
  Equiv.ofBijective letterToBasic (letterToBasic_bijective n)

theorem blocks_parameter_one :
    core .c = [Finset.univ] ∧ core (.arm false 0) = [{2}] ∧ core (.arm true 0) = [{0}] ∧
    Fintype.card (Grade weight 1) = 3 := by simp [core,single]

theorem empty_word_unique (W : Word 0) : W.val = [] := by
  cases h : W.val with
  | nil => rfl
  | cons a U =>
    have hm := W.property
    rw [h,mass_cons] at hm
    have := weight_pos a
    omega

theorem empty_position_complete (W : List Letter) (k : ℕ) (hk : k≤2*mass W)
    (he : (∅ :: trace W).getD k ∅ = ∅) : ∃ U V, W=U++V ∧ k=2*mass U := by
  induction W generalizing k with
  | nil => exact ⟨[],[],rfl,by simpa using hk⟩
  | cons a W ih =>
    cases k with
    | zero => exact ⟨[],a::W,rfl,rfl⟩
    | succ k =>
      change (trace (a::W)).getD k ∅ = ∅ at he
      rw [trace_cons] at he
      have hc := core_length a
      by_cases hl : k < (core a).length
      · rw [List.getD_append _ _ _ _ hl,List.getD_eq_getElem _ _ hl] at he
        exact (empty_not_mem_core a (he ▸ List.getElem_mem hl)).elim
      · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hl)] at he
        have hbound : k-(core a).length ≤ 2*mass W := by simp only [mass_cons] at hk; omega
        obtain ⟨U,V,hW,hk'⟩ := ih _ hbound he
        refine ⟨a::U,V,by simp [hW],?_⟩
        simp only [mass_cons]
        omega

theorem empty_position_sound (U V : List Letter) :
    (∅ :: trace (U++V)).getD (2*mass U) ∅ = ∅ := by
  rw [trace_append,← List.cons_append]
  rw [List.getD_append _ _ _ _ (by simp)]
  have h := ((valid_iff_getD ∅ (trace U)).mp (valid_trace U)).1
  simpa only [trace_length] using h

theorem all_cuts_are_block_boundaries (W : List Letter) (k : ℕ) (hk : k≤2*mass W) :
    (∅ :: trace W).getD k ∅ = ∅ ↔ ∃ U V, W=U++V ∧ k=2*mass U := by
  constructor
  · exact empty_position_complete W k hk
  · rintro ⟨U,V,rfl,rfl⟩
    exact empty_position_sound U V

end Domino.Blocks
