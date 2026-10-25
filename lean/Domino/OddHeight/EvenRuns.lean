module

public import Domino.OddHeight.Column

/-! 连续空行段的偶长条件：扫描时越过占用行，在空行段内每次取相邻两行。
这一独立的语法条件不提及铺法或配对关系；下面证明它与列可铺性等价。 -/

@[expose] public section

namespace Domino.General

inductive EvenRuns (free : ℕ → Prop) : ℕ → ℕ → Prop
  | nil (a : ℕ) : EvenRuns free a 0
  | blocked {a n : ℕ} : ¬free a → EvenRuns free (a + 1) n → EvenRuns free a (n + 1)
  | pair {a n : ℕ} : free a → free (a + 1) → EvenRuns free (a + 2) n → EvenRuns free a (n + 2)

def IntervalCover (free : ℕ → Prop) (a n : ℕ) (R : ℕ → ℕ → Prop) : Prop :=
  (∀ r s, R r s → r + 1 = s ∨ s + 1 = r) ∧
  (∀ r s, R r s → R s r) ∧
  (∀ r, (∃ s, R r s) ↔ a ≤ r ∧ r < a + n ∧ free r) ∧
  (∀ r s t, R r s → R r t → s = t)

theorem interval_cover_even_runs (free : ℕ → Prop) (a n : ℕ) (R : ℕ → ℕ → Prop)
    (h : IntervalCover free a n R) : EvenRuns free a n := by
  induction n using Nat.strong_induction_on generalizing a R with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; exact .nil a
    by_cases hf : free a
    · obtain ⟨s, has⟩ := (h.2.2.1 a).mpr ⟨le_rfl, by omega, hf⟩
      have hs := (h.2.2.1 s).mp ⟨a, h.2.1 a s has⟩
      have hadj := h.1 a s has
      have he : s = a + 1 := by omega
      subst s
      have hlen : 2 ≤ n := by omega
      let R' := fun r s => R r s ∧ a + 2 ≤ r ∧ a + 2 ≤ s
      have htail : IntervalCover free (a + 2) (n - 2) R' := by
        refine ⟨fun r s hrs => h.1 r s hrs.1,
          fun r s hrs => ⟨h.2.1 r s hrs.1, hrs.2.2, hrs.2.1⟩, ?_,
          fun r s t hrs hrt => h.2.2.2 r s t hrs.1 hrt.1⟩
        intro r
        constructor
        · rintro ⟨s, hrs⟩
          have hr := (h.2.2.1 r).mp ⟨s, hrs.1⟩
          exact ⟨hrs.2.1, by omega, hr.2.2⟩
        · rintro ⟨hr, hrn, hfr⟩
          obtain ⟨s, hrs⟩ := (h.2.2.1 r).mpr ⟨by omega, by omega, hfr⟩
          have hsr := h.2.1 r s hrs
          have hs0 := (h.2.2.1 s).mp ⟨r, hsr⟩
          have hs2 : a + 2 ≤ s := by
            by_contra hn
            have he : s = a ∨ s = a + 1 := by omega
            rcases he with he | he
            · subst s
              have := h.2.2.2 a r (a + 1) hsr has
              omega
            · subst s
              have := h.2.2.2 (a + 1) r a hsr (h.2.1 a (a + 1) has)
              omega
          exact ⟨s, hrs, hr, hs2⟩
      have ht := ih (n - 2) (by omega) (a + 2) R' htail
      have hp := EvenRuns.pair hf hs.2.2 ht
      simpa [show n - 2 + 2 = n by omega] using hp
    · have htail : IntervalCover free (a + 1) (n - 1) R := by
        refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
        intro r
        rw [h.2.2.1]
        constructor
        · rintro ⟨hr, hrn, hfr⟩
          have : r ≠ a := by intro he; subst r; exact hf hfr
          exact ⟨by omega, by omega, hfr⟩
        · rintro ⟨hr, hrn, hfr⟩; exact ⟨by omega, by omega, hfr⟩
      have ht := EvenRuns.blocked hf (ih (n - 1) (by omega) (a + 1) R htail)
      simpa [show n - 1 + 1 = n by omega] using ht

theorem even_runs_interval_cover {free : ℕ → Prop} {a n : ℕ} (h : EvenRuns free a n) :
    ∃ R, IntervalCover free a n R := by
  induction h with
  | nil a => exact ⟨fun _ _ => False, by simp [IntervalCover]; omega⟩
  | @blocked a n hf _ ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨R, hR.1, hR.2.1, ?_, hR.2.2.2⟩
    intro r
    rw [hR.2.2.1]
    constructor
    · rintro ⟨hr, hrn, hfr⟩; exact ⟨by omega, by omega, hfr⟩
    · rintro ⟨hr, hrn, hfr⟩
      have : r ≠ a := by intro he; subst r; exact hf hfr
      exact ⟨by omega, by omega, hfr⟩
  | @pair a n hf hg _ ih =>
    obtain ⟨R, hR⟩ := ih
    let W := fun r s => (r = a ∧ s = a + 1) ∨ (r = a + 1 ∧ s = a) ∨ R r s
    have small (r s : ℕ) (hrs : R r s) : a + 2 ≤ r ∧ a + 2 ≤ s :=
      ⟨((hR.2.2.1 r).mp ⟨s, hrs⟩).1, ((hR.2.2.1 s).mp ⟨r, hR.2.1 r s hrs⟩).1⟩
    refine ⟨W, ?_, ?_, ?_, ?_⟩
    · intro r s hrs
      rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hrs
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact hR.1 r s hrs
    · intro r s hrs
      rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hrs
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (hR.2.1 r s hrs))
    · intro r
      constructor
      · rintro ⟨s, hrs⟩
        rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hrs
        · exact ⟨by omega, by omega, hf⟩
        · exact ⟨by omega, by omega, hg⟩
        · have hr := (hR.2.2.1 r).mp ⟨s, hrs⟩
          exact ⟨by omega, by omega, hr.2.2⟩
      · rintro ⟨hr, hrn, hfr⟩
        by_cases he : r = a
        · subst r; exact ⟨a + 1, Or.inl ⟨rfl, rfl⟩⟩
        by_cases he' : r = a + 1
        · subst r; exact ⟨a, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
        obtain ⟨s, hrs⟩ := (hR.2.2.1 r).mpr ⟨by omega, by omega, hfr⟩
        exact ⟨s, Or.inr (Or.inr hrs)⟩
    · intro r s t hrs hrt
      rcases hrs with hrs | hrs | hrs <;> rcases hrt with hrt | hrt | hrt
      all_goals first | exact hR.2.2.2 r s t hrs hrt | (have := small r s hrs; omega) |
        (have := small r t hrt; omega) | omega

@[simp] theorem row_mem_val_image {m : ℕ} (H : State m) (r : Fin m) :
    r.val ∈ H.image Fin.val ↔ r ∈ H := by
  constructor
  · intro h
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp h
    have : s = r := Fin.ext he
    simpa [this] using hs
  · exact fun h => Finset.mem_image.mpr ⟨r, h, rfl⟩

theorem row_cover_iff_even_runs {m : ℕ} (H : State m) :
    Nonempty (RowCover H) ↔ EvenRuns (fun r => r ∉ H.image Fin.val) 0 m := by
  classical
  constructor
  · rintro ⟨⟨V, hV⟩⟩
    let R := fun r s => ∃ hr : r < m, ∃ hs : s < m, (⟨r, hr⟩, ⟨s, hs⟩) ∈ V
    apply interval_cover_even_runs _ 0 m R
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro r s ⟨hr, hs, hrs⟩; exact hV.1 ⟨r, hr⟩ ⟨s, hs⟩ hrs
    · rintro r s ⟨hr, hs, hrs⟩; exact ⟨hs, hr, hV.2.1 _ _ hrs⟩
    · intro r
      constructor
      · rintro ⟨s, hr, hs, hrs⟩
        have hfree := (hV.2.2.1 ⟨r, hr⟩).mp ⟨⟨s, hs⟩, hrs⟩
        refine ⟨by omega, by omega, ?_⟩
        exact fun hh => hfree ((row_mem_val_image H ⟨r, hr⟩).mp hh)
      · rintro ⟨_, hr, hfree⟩
        have hr' : r < m := by omega
        have hfree' : (⟨r, hr'⟩ : Fin m) ∉ H :=
          fun hh => hfree ((row_mem_val_image H ⟨r, hr'⟩).mpr hh)
        obtain ⟨s, hrs⟩ := (hV.2.2.1 ⟨r, hr'⟩).mpr hfree'
        exact ⟨s.val, hr', s.isLt, hrs⟩
    · rintro r s t ⟨hr, hs, hrs⟩ ⟨_, ht, hrt⟩
      exact congrArg Fin.val (hV.2.2.2 ⟨r, hr⟩ ⟨s, hs⟩ ⟨t, ht⟩ hrs hrt)
  · intro h
    obtain ⟨R, hR⟩ := even_runs_interval_cover h
    let V : RowBonds m := Finset.univ.filter fun rs => R rs.1.val rs.2.val
    have mem (r s : Fin m) : (r, s) ∈ V ↔ R r.val s.val := by simp [V]
    refine ⟨⟨V, ?_, ?_, ?_, ?_⟩⟩
    · intro r s hrs; exact hR.1 _ _ ((mem r s).mp hrs)
    · intro r s hrs; exact (mem s r).mpr (hR.2.1 _ _ ((mem r s).mp hrs))
    · intro r
      constructor
      · rintro ⟨s, hrs⟩
        have hf := ((hR.2.2.1 r.val).mp ⟨s.val, (mem r s).mp hrs⟩).2.2
        exact fun hh => hf ((row_mem_val_image H r).mpr hh)
      · intro hf
        have hfree : r.val ∉ H.image Fin.val := fun hh => hf ((row_mem_val_image H r).mp hh)
        obtain ⟨s, hrs⟩ := (hR.2.2.1 r.val).mpr ⟨by omega, by simp, hfree⟩
        have hs := (hR.2.2.1 s).mp ⟨r.val, hR.2.1 _ _ hrs⟩
        exact ⟨⟨s, by omega⟩, (mem _ _).mpr hrs⟩
    · intro r s t hrs hrt
      exact Fin.ext (hR.2.2.2 _ _ _ ((mem r s).mp hrs) ((mem r t).mp hrt))

theorem legal_iff_even_runs {m : ℕ} (p q : State m) :
    Legal p q ↔ Disjoint p q ∧ EvenRuns (fun r => r ∉ (p ∪ q).image Fin.val) 0 m := by
  rw [Legal, row_cover_iff_even_runs]

theorem even_runs_all_free {a n : ℕ} (h : EvenRuns (fun _ => True) a n) : Even n := by
  induction h with
  | nil => exact ⟨0, rfl⟩
  | blocked hf => exact False.elim (hf trivial)
  | pair _ _ _ ih => exact ih.add (by decide : Even 2)

/-- pending 表示当前连续空行段的已扫描长度为奇数；占用行及末端要求偶数。 -/
def evenRunScan (free : ℕ → Bool) (pending : Bool) (a : ℕ) : ℕ → Bool
  | 0 => !pending
  | n + 1 => if free a then evenRunScan free (!pending) (a + 1) n
      else !pending && evenRunScan free false (a + 1) n

theorem even_runs_scan {free : ℕ → Bool} {a n : ℕ}
    (h : EvenRuns (fun r => free r = true) a n) : evenRunScan free false a n = true := by
  induction h with
  | nil => rfl
  | blocked hf _ ih => simpa [evenRunScan, hf] using ih
  | @pair a n hf hg _ ih =>
    simpa [evenRunScan, hf, hg, Nat.add_assoc] using ih

theorem scan_even_runs (free : ℕ → Bool) (a n : ℕ)
    (h : evenRunScan free false a n = true) : EvenRuns (fun r => free r = true) a n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases n with
    | zero => exact .nil a
    | succ n =>
      by_cases hf : free a = true
      · cases n with
        | zero => simp [evenRunScan, hf] at h
        | succ n =>
          have hg : free (a + 1) = true := by
            by_contra hn
            simp [evenRunScan, hf, hn] at h
          have ht : evenRunScan free false (a + 2) n = true := by
            simpa [evenRunScan, hf, hg, Nat.add_assoc] using h
          exact .pair hf hg (ih n (by omega) (a + 2) ht)
      · have ht : evenRunScan free false (a + 1) n = true := by
          simpa [evenRunScan, hf] using h
        exact .blocked hf (ih n (by omega) (a + 1) ht)

theorem legal_iff_even_run_scan {m : ℕ} (p q : State m) :
    Legal p q ↔ Disjoint p q ∧
      evenRunScan (fun r => decide (r ∉ (p ∪ q).image Fin.val)) false 0 m = true := by
  rw [legal_iff_even_runs]
  constructor
  · rintro ⟨hd, h⟩
    exact ⟨hd, even_runs_scan (by simpa only [decide_eq_true_eq] using h)⟩
  · rintro ⟨hd, h⟩
    exact ⟨hd, by simpa only [decide_eq_true_eq] using scan_even_runs _ _ _ h⟩

end Domino.General
