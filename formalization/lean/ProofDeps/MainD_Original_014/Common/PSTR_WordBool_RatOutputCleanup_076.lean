module

public import Common.PSTR_WordBool_RatOutputFields_075

/-! Actual finite-cell cleanup and reversal; no quotient equality erases
a cell. A local segment joins the real phase paths without duplicate steps. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatOutput

open Turing

variable {C : Type*}

def clearState (rightSide : Bool) (background : Stack → List Bool) (point : Label) (context : C) (memory : Store)
    (remaining fixed counter target : List Bool) : State C :=
  if rightSide then state background point context memory remaining fixed counter target
  else state background point context memory fixed remaining counter target

def clearTrace (rightSide : Bool) (background : Stack → List Bool) (context : C) :
    List Bool → Store → List Bool → List Bool → List Bool → List (State C)
  | [],memory,fixed,counter,target =>
      [clearState rightSide background (if rightSide then 6 else 0) context memory [] fixed counter target,
       clearState rightSide background (if rightSide then 7 else 1) context (false,false) [] fixed counter target]
  | cell::later,memory,fixed,counter,target =>
      clearState rightSide background (if rightSide then 6 else 0) context memory (cell::later) fixed counter target ::
      clearTrace rightSide background context later (true,cell) fixed counter target

theorem clear_head (rightSide : Bool) (background : Stack → List Bool) (context : C) (remaining : List Bool)
    (memory : Store) (fixed counter target : List Bool) :
    (clearTrace rightSide background context remaining memory fixed counter target).head? =
      some (clearState rightSide background (if rightSide then 6 else 0) context memory remaining fixed counter target) := by
  cases remaining <;> rfl

theorem clear_nonempty (rightSide : Bool) (background : Stack → List Bool) (context : C) (remaining : List Bool)
    (memory : Store) (fixed counter target : List Bool) :
    clearTrace rightSide background context remaining memory fixed counter target ≠ [] := by
  cases remaining <;> intro same <;> cases same

theorem clear_last (rightSide : Bool) (background : Stack → List Bool) (context : C) (remaining : List Bool)
    (memory : Store) (fixed counter target : List Bool) :
    (clearTrace rightSide background context remaining memory fixed counter target).getLast? =
      some (clearState rightSide background (if rightSide then 7 else 1) context (false,false) [] fixed counter target) := by
  induction remaining generalizing memory with
  | nil => rfl
  | cons cell later ih =>
    rw [clearTrace,List.getLast?_cons_of_ne_nil (clear_nonempty _ _ _ _ _ _ _ _),ih]

theorem clear_chain (caller : Statement C) (rightSide : Bool) (background : Stack → List Bool) (context : C)
    (remaining : List Bool) (memory : Store) (fixed counter target : List Bool) :
    (clearTrace rightSide background context remaining memory fixed counter target).IsChain
      (fun a b => TM2.step (program caller) a = some b) := by
  induction remaining generalizing memory with
  | nil =>
    apply List.isChain_cons_cons.mpr
    refine ⟨?_,List.isChain_singleton _⟩
    cases rightSide
    · exact clear_left_done caller background context memory fixed counter target
    · exact clear_right_done caller background context memory fixed counter target
  | cons cell later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (true,cell)⟩
    intro next member
    rw [clear_head] at member
    have same : next = _ := (Option.mem_some_iff.mp member).symm
    subst next
    cases rightSide
    · exact clear_left_step caller background context memory cell fixed later counter target
    · exact clear_right_step caller background context memory cell later fixed counter target

theorem clear_length (rightSide : Bool) (background : Stack → List Bool) (context : C) (remaining : List Bool)
    (memory : Store) (fixed counter target : List Bool) :
    (clearTrace rightSide background context remaining memory fixed counter target).length = remaining.length+2 := by
  induction remaining generalizing memory with
  | nil => rfl
  | cons cell later ih => simp only [clearTrace,List.length_cons,ih]

theorem clear_state_safe (rightSide : Bool) (background : Stack → List Bool) (point : Label) (context : C)
    (memory : Store) (remaining fixed counter target : List Bool) :
    Safe background context (outside background + remaining.length + fixed.length + counter.length + target.length)
      (clearState rightSide background point context memory remaining fixed counter target) := by
  cases rightSide <;> apply safe_state <;> omega

theorem clear_safe (rightSide : Bool) (background : Stack → List Bool) (context : C) (remaining : List Bool)
    (memory : Store) (fixed counter target : List Bool) :
    ∀ current ∈ clearTrace rightSide background context remaining memory fixed counter target,
      Safe background context (outside background + remaining.length + fixed.length + counter.length + target.length) current := by
  induction remaining generalizing memory with
  | nil =>
    intro current member
    simp only [clearTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals exact clear_state_safe rightSide background _ context _ [] fixed counter target
  | cons cell later ih =>
    intro current member
    rcases List.mem_cons.mp member with same | remaining
    · subst current
      exact clear_state_safe rightSide background _ context _ (cell::later) fixed counter target
    · exact safe_mono (ih (true,cell) current remaining) (by simp only [List.length_cons]; omega)

def reverseTrace (background : Stack → List Bool) (context : C) :
    List Bool → Store → List Bool → List Bool → List Bool → List (State C)
  | [],memory,right,counter,target =>
      [state background 7 context memory right [] counter target,
       state background 8 context (false,false) right [] counter target]
  | cell::later,memory,right,counter,target =>
      state background 7 context memory right (cell::later) counter target ::
      reverseTrace background context later (true,cell) right counter (cell::target)

theorem reverse_head (background : Stack → List Bool) (context : C) (left : List Bool) (memory : Store)
    (right counter target : List Bool) :
    (reverseTrace background context left memory right counter target).head? =
      some (state background 7 context memory right left counter target) := by cases left <;> rfl

theorem reverse_nonempty (background : Stack → List Bool) (context : C) (left : List Bool) (memory : Store)
    (right counter target : List Bool) : reverseTrace background context left memory right counter target ≠ [] := by
  cases left <;> intro same <;> cases same

theorem reverse_last (background : Stack → List Bool) (context : C) (left : List Bool) (memory : Store)
    (right counter target : List Bool) :
    (reverseTrace background context left memory right counter target).getLast? =
      some (state background 8 context (false,false) right [] counter (left.reverse++target)) := by
  induction left generalizing memory target with
  | nil => rfl
  | cons cell later ih =>
    rw [reverseTrace,List.getLast?_cons_of_ne_nil (reverse_nonempty _ _ _ _ _ _ _),ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem reverse_chain (caller : Statement C) (background : Stack → List Bool) (context : C) (left : List Bool)
    (memory : Store) (right counter target : List Bool) :
    (reverseTrace background context left memory right counter target).IsChain
      (fun a b => TM2.step (program caller) a = some b) := by
  induction left generalizing memory target with
  | nil => exact List.isChain_cons_cons.mpr ⟨reverse_done caller background context memory right counter target,
      List.isChain_singleton _⟩
  | cons cell later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (true,cell) (cell::target)⟩
    intro next member
    rw [reverse_head] at member
    have same : next = _ := (Option.mem_some_iff.mp member).symm
    subst next
    exact reverse_step caller background context memory cell right later counter target

theorem reverse_length (background : Stack → List Bool) (context : C) (left : List Bool) (memory : Store)
    (right counter target : List Bool) :
    (reverseTrace background context left memory right counter target).length = left.length+2 := by
  induction left generalizing memory target with
  | nil => rfl
  | cons cell later ih => simp only [reverseTrace,List.length_cons,ih]

theorem reverse_safe (background : Stack → List Bool) (context : C) (left : List Bool) (memory : Store)
    (right counter target : List Bool) :
    ∀ current ∈ reverseTrace background context left memory right counter target,
      Safe background context (outside background + right.length + left.length + counter.length + target.length) current := by
  induction left generalizing memory target with
  | nil =>
    intro current member
    simp only [reverseTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals apply safe_state
    all_goals exact Nat.le_refl _
  | cons cell later ih =>
    intro current member
    rcases List.mem_cons.mp member with same | remaining
    · subst current
      apply safe_state
      exact Nat.le_refl _
    · exact safe_mono (ih (true,cell) (cell::target) current remaining) (by simp only [List.length_cons]; omega)

structure Segment (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bound : Nat) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head? = some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a = some b)
  last : trace.getLast? = some final
  count : trace.length ≤ budget
  safe : ∀ current ∈ trace, Safe background context bound current

def Segment.append {caller : Statement C} {background : Stack → List Bool} {context : C} {bound : Nat}
    {before middle final : State C} {frontBudget backBudget : Nat}
    (front : Segment caller background context bound before middle frontBudget)
    (back : Segment caller background context bound middle final backBudget) :
    Segment caller background context bound before final (frontBudget+backBudget-1) := by
  have shape : middle::back.trace.tail = back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.head
    rw [same]
    rfl
  have backLength := congrArg List.length shape
  simp only [List.length_cons] at backLength
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have a := front.count; have b := back.count
    simp only [List.length_append]
    omega
  · intro current member
    rcases List.mem_append.mp member with early | later
    · exact front.safe current early
    · exact back.safe current (List.mem_of_mem_tail later)

end PaperProofs.Common.Native.PSTRWordBool.RatOutput
