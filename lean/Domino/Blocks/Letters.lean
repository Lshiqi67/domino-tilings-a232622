module

public import Domino.Symmetry.PathAction
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Palindrome

/-! A02 的字母与逐列编码。arm false k = A_(k+1)，arm true k = B_(k+1)。 -/

@[expose] public section
namespace Domino.Blocks

inductive Letter where
  | c
  | arm (side : Bool) (extra : ℕ)
  deriving DecidableEq

def weight : Letter → ℕ
  | .c => 1
  | .arm _ k => k + 1

def flip : Letter → Letter
  | .c => .c
  | .arm b k => .arm (!b) k

@[simp] theorem flip_flip (a : Letter) : flip (flip a) = a := by cases a <;> simp [flip]
@[simp] theorem weight_flip (a : Letter) : weight (flip a) = weight a := by cases a <;> rfl
theorem weight_pos (a : Letter) : 0 < weight a := by cases a <;> simp [weight]

def single (b : Bool) : State 3 := if b then {0} else {2}
def paired (b : Bool) : State 3 := if b then {1, 2} else {0, 1}

theorem single_ne_empty (b : Bool) : single b ≠ ∅ := by cases b <;> decide
theorem paired_ne_empty (b : Bool) : paired b ≠ ∅ := by cases b <;> decide
theorem single_ne_univ (b : Bool) : single b ≠ Finset.univ := by cases b <;> decide
theorem single_injective : Function.Injective single := by decide
@[simp] theorem reverse_single (b : Bool) : reverseState (single b) = single (!b) := by cases b <;> decide
@[simp] theorem reverse_paired (b : Bool) : reverseState (paired b) = paired (!b) := by cases b <;> decide

def core : Letter → List (State 3)
  | .c => [Finset.univ]
  | .arm b 0 => [single b]
  | .arm b (k + 1) => single b :: paired b :: core (.arm b k)

def trace (W : List Letter) : List (State 3) := W.flatMap fun a => core a ++ [∅]
def mass (W : List Letter) : ℕ := (W.map weight).sum

@[simp] theorem mass_nil : mass [] = 0 := rfl
@[simp] theorem mass_cons (a : Letter) (W : List Letter) : mass (a :: W) = weight a + mass W := rfl
@[simp] theorem mass_append (U V : List Letter) : mass (U ++ V) = mass U + mass V := by simp [mass]
@[simp] theorem trace_nil : trace [] = [] := rfl
@[simp] theorem trace_cons (a : Letter) (W : List Letter) : trace (a :: W) = core a ++ ∅ :: trace W := by simp [trace]
@[simp] theorem trace_append (U V : List Letter) : trace (U ++ V) = trace U ++ trace V := by simp [trace]

theorem core_length (a : Letter) : (core a).length + 1 = 2 * weight a := by
  cases a with
  | c => simp [core, weight]
  | arm b k => induction k with
    | zero => simp [core, weight]
    | succ k ih => simp only [core, List.length_cons, weight] at *; omega

@[simp] theorem trace_length (W : List Letter) : (trace W).length = 2 * mass W := by
  induction W with
  | nil => rfl
  | cons a W ih => simp only [trace_cons, List.length_append, List.length_cons, ih, mass_cons]; have := core_length a; omega

theorem core_nonempty (a : Letter) : core a ≠ [] := by
  cases a with
  | c => simp [core]
  | arm b k => cases k <;> simp [core]

theorem empty_not_mem_core (a : Letter) : (∅ : State 3) ∉ core a := by
  cases a with
  | c => simp only [core, List.mem_singleton]; decide
  | arm b k => induction k with
    | zero => simpa [core] using (single_ne_empty b).symm
    | succ k ih => simp [core, ih, Ne.symm (single_ne_empty b), Ne.symm (paired_ne_empty b)]

def decode : List (State 3) → List Letter
  | q :: r :: L =>
      if r = ∅ then (if q = Finset.univ then Letter.c else Letter.arm (q = single true) 0) :: decode L
      else match decode L with
        | .arm b k :: W => .arm b (k + 1) :: W
        | _ => []
  | _ => []

theorem decode_core (a : Letter) (W : List Letter) : decode (core a ++ ∅ :: trace W) = a :: decode (trace W) := by
  cases a with
  | c => simp [core, decode]
  | arm b k =>
    induction k with
    | zero => cases b <;> simp [core, decode, single]
    | succ k ih => simp only [core, List.cons_append, decode, paired_ne_empty, ite_false]; rw [ih]

@[simp] theorem decode_trace (W : List Letter) : decode (trace W) = W := by
  induction W with
  | nil => rfl
  | cons a W ih => rw [trace_cons, decode_core, ih]

theorem trace_injective : Function.Injective trace := by
  intro U V h
  simpa using congrArg decode h

theorem core_arm_snoc (b : Bool) (k : ℕ) :
    core (.arm b (k + 1)) = core (.arm b k) ++ [paired b, single b] := by
  induction k with
  | zero => simp [core]
  | succ k ih => simpa only [core, List.cons_append] using congrArg (fun L => single b :: paired b :: L) ih

@[simp] theorem core_reverse (a : Letter) : (core a).reverse = core a := by
  cases a with
  | c => simp [core]
  | arm b k =>
    induction k with
    | zero => simp [core]
    | succ k ih => rw [core, List.reverse_cons, List.reverse_cons, ih]; simpa only [core, List.append_assoc, List.singleton_append] using (core_arm_snoc b k).symm

@[simp] theorem core_flip (a : Letter) : (core a).map reverseState = core (flip a) := by
  cases a with
  | c => simp only [core, flip, List.map_cons, List.map_nil, List.cons.injEq, and_true]; decide
  | arm b k => induction k with
    | zero => simp [core, flip]
    | succ k ih => simp only [core, List.map_cons, reverse_single, reverse_paired, flip] at *; rw [ih]

@[simp] theorem trace_flip (W : List Letter) : (trace W).map reverseState = trace (W.map flip) := by
  induction W with
  | nil => rfl
  | cons a W ih => simp [trace_cons, ih]

@[simp] theorem full_reverse (W : List Letter) : (∅ :: trace W).reverse = ∅ :: trace W.reverse := by
  induction W with
  | nil => rfl
  | cons a W ih =>
    have h := congrArg (fun L => L ++ core a ++ [∅]) ih
    simpa [List.reverse_cons, List.reverse_append, trace_cons, core_reverse, List.append_assoc] using h

@[simp] theorem mass_flip (W : List Letter) : mass (W.map flip) = mass W := by simp [mass, List.map_map, Function.comp_def]
@[simp] theorem mass_reverse (W : List Letter) : mass W.reverse = mass W := by simp [mass, List.map_reverse]

end Domino.Blocks
