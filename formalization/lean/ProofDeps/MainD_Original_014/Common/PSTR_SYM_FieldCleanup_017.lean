module

public import Common.PSTR_SYM_ReverseErase_016

/-! The field's own END cell is the actual return marker. The next tag
and whole suffix are never modified, so an original EOF TRUE is supported.
No second OWN false, supplied field length or cursor reset is required. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCleanup

open Turing PSTRTMRawNat010 PSTRTMSeq005
open PSTRSymbolicErase (coreTrace core_head core_last core_chain core_length)

def cleanupMachine : Machine 9 := fun label symbol =>
  match label.val with
  | 0 => some (1, .move .left)
  | 1 => some (6, .write true)
  | 2 => if symbol then some (3, .write false) else some (7, .move .right)
  | 3 => some (4, .move .left)
  | 4 => some (5, .write false)
  | 5 => some (2, .move .left)
  | 6 => some (2, .move .left)
  | 7 => if symbol then some (8, .write false) else some (7, .move .right)
  | 8 => some (9, .move .right)
  | _ => none

def state (label : Fin 10) (left right : List Bool) : MachineState 9 :=
  ⟨label, Tape.mk₂ left right⟩

def embed (before : MachineState 5) : MachineState 9 :=
  ⟨⟨before.q.val, by have bound := before.q.isLt; omega⟩, before.Tape⟩

theorem core_lower (archive cleared digits : List Bool) :
    ∀ before ∈ coreTrace archive cleared digits, 2 ≤ before.q.val := by
  induction digits generalizing cleared with
  | nil =>
    intro before member
    simp only [coreTrace, List.mem_singleton] at member
    subst before
    simp [PSTRSymbolicErase.state]
  | cons bit later ih =>
    intro before member
    rcases List.mem_append.mp member with member | member
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | member | member | member <;>
        subst before <;> simp [PSTRSymbolicErase.state]
    · exact ih _ before member

theorem cleanup_step_embed (before after : MachineState 5) (lower : 2 ≤ before.q.val)
    (actual : TM0.step PSTRSymbolicErase.backwardMachine before = some after) :
    TM0.step cleanupMachine (embed before) = some (embed after) := by
  have same : TM0.step cleanupMachine (embed before) =
      (TM0.step PSTRSymbolicErase.backwardMachine before).map embed := by
    rcases before with ⟨⟨label, fit⟩, tape⟩
    have below : label ≤ 5 := by omega
    interval_cases label <;> cases head : tape.head <;>
      simp_all [TM0.step, cleanupMachine, embed, PSTRSymbolicErase.backwardMachine]
    all_goals
      subst after
      exact ⟨rfl, rfl⟩
  rw [same, actual]
  rfl

theorem cleanup_core_chain (archive cleared digits : List Bool) :
    ((coreTrace archive cleared digits).map embed).IsChain
      (fun before after => TM0.step cleanupMachine before = some after) := by
  apply (List.isChain_map _).mpr
  apply (core_chain archive cleared digits).imp_of_mem_imp
  intro before after beforeMember _ actual
  exact cleanup_step_embed before after (core_lower archive cleared digits before beforeMember) actual

def returnTrace (archive suffix : List Bool) : Nat → List (MachineState 9)
  | 0 => [state 7 archive (true :: suffix), state 8 archive (false :: suffix),
      state 9 (false :: archive) suffix]
  | count + 1 => state 7 archive (false :: (List.replicate count false ++ true :: suffix)) ::
      returnTrace (false :: archive) suffix count

theorem return_head (archive suffix : List Bool) (count : Nat) :
    (returnTrace archive suffix count).head? =
      some (state 7 archive (List.replicate count false ++ true :: suffix)) := by
  cases count <;> rfl

theorem zero_push (count : Nat) (archive : List Bool) :
    List.replicate count false ++ false :: archive =
      List.replicate (count + 1) false ++ archive := by
  rw [List.replicate_add]
  simp [List.append_assoc]

theorem return_last (archive suffix : List Bool) (count : Nat) :
    (returnTrace archive suffix count).getLast? =
      some (state 9 (List.replicate (count + 1) false ++ archive) suffix) := by
  induction count generalizing archive with
  | zero => rfl
  | succ count ih =>
    have nonempty : returnTrace (false :: archive) suffix count ≠ [] := by
      intro empty
      have head := return_head (false :: archive) suffix count
      simp only [empty, List.head?_nil, reduceCtorEq] at head
    rw [returnTrace, List.getLast?_cons_of_ne_nil nonempty, ih, zero_push]

theorem return_chain (archive suffix : List Bool) (count : Nat) :
    (returnTrace archive suffix count).IsChain
      (fun before after => TM0.step cleanupMachine before = some after) := by
  induction count generalizing archive with
  | zero =>
    simp [returnTrace, List.isChain_cons_cons, TM0.step, cleanupMachine, state, Tape.mk₂]
  | succ count ih =>
    rw [returnTrace]
    apply List.isChain_cons.mpr
    refine ⟨?_, ih _⟩
    intro after afterHead
    rw [return_head] at afterHead
    have equal := Option.mem_some_iff.mp afterHead
    subst after
    simp [TM0.step, cleanupMachine, state, Tape.mk₂]

theorem return_length (archive suffix : List Bool) (count : Nat) :
    (returnTrace archive suffix count).length = count + 3 := by
  induction count generalizing archive with
  | zero => rfl
  | succ count ih =>
    rw [returnTrace, List.length_cons, ih]

def cleanupTrace (archive digits suffix : List Bool) : List (MachineState 9) :=
  [state 0 (false :: (leftBlocks digits.reverse ++ false :: archive)) suffix,
    state 1 (leftBlocks digits.reverse ++ false :: archive) (false :: suffix),
    state 6 (leftBlocks digits.reverse ++ false :: archive) (true :: suffix)] ++
      ((coreTrace archive (true :: suffix) digits.reverse).map embed ++
        returnTrace (false :: archive) suffix (2 * digits.length))

def cleanupFinal (archive digits suffix : List Bool) : MachineState 9 :=
  state 9 (List.replicate (2 * digits.length + 2) false ++ archive) suffix

theorem cleanup_runsFrom (archive digits suffix : List Bool) :
    RunsFrom cleanupMachine
      (state 0 (false :: (leftBlocks digits.reverse ++ false :: archive)) suffix)
      (cleanupTrace archive digits suffix) (cleanupFinal archive digits suffix) := by
  have middle := cleanup_core_chain archive (true :: suffix) digits.reverse
  have back := return_chain (false :: archive) suffix (2 * digits.length)
  have joined := middle.append back (by
    intro before beforeLast after afterHead
    simp only [List.getLast?_map, core_last, Option.map_some, Option.mem_some_iff] at beforeLast
    rw [return_head] at afterHead
    have equal := Option.mem_some_iff.mp afterHead
    subst before
    subst after
    simp [embed, PSTRSymbolicErase.state, state, List.length_reverse,
      TM0.step, cleanupMachine, Tape.mk₂])
  refine ⟨rfl, ?_, ?_, ?_⟩
  · let front :=
      [state 0 (false :: (leftBlocks digits.reverse ++ false :: archive)) suffix,
        state 1 (leftBlocks digits.reverse ++ false :: archive) (false :: suffix),
        state 6 (leftBlocks digits.reverse ++ false :: archive) (true :: suffix)]
    have chain : front.IsChain (fun before after => TM0.step cleanupMachine before = some after) := by
      simp [front, List.isChain_cons_cons, TM0.step, cleanupMachine, state, Tape.mk₂]
    change (front ++ _).IsChain _
    apply chain.append joined
    intro before beforeLast after afterHead
    have last : front.getLast? = some
        (state 6 (leftBlocks digits.reverse ++ false :: archive) (true :: suffix)) := rfl
    rw [last] at beforeLast
    simp only [List.head?_append, List.head?_map, core_head, Option.map_some,
      Option.some_or, Option.mem_some_iff] at afterHead
    have equal := Option.mem_some_iff.mp beforeLast
    subst before
    subst after
    cases digits.reverse <;>
      simp [embed, PSTRSymbolicErase.state, state, TM0.step, cleanupMachine, Tape.mk₂, leftBlocks]
  · rw [cleanupTrace, List.getLast?_append, List.getLast?_append, return_last, Option.some_or,
      Option.some_or, zero_push]
    rfl
  · simp [cleanupFinal, state, TM0.step, cleanupMachine]

theorem cleanup_final_tape (archive digits suffix : List Bool) :
    (cleanupFinal archive digits suffix).Tape =
      Tape.mk₂ (List.replicate (2 * digits.length + 2) false ++ archive) suffix := rfl

theorem cleanup_length (archive digits suffix : List Bool) :
    (cleanupTrace archive digits suffix).length = 6 * digits.length + 7 := by
  simp only [cleanupTrace, List.length_append, List.length_map, core_length,
    return_length, List.length_reverse, List.length_cons, List.length_nil]
  omega

theorem cleanup_space (archive digits suffix : List Bool) (inputLength : Nat) :
    visitedSpace cleanupMachine inputLength (cleanupTrace archive digits suffix) ≤
      inputLength + 12 * digits.length + 15 := by
  have bound := PSTRTMTrace002.visitedSpace_le cleanupMachine inputLength
    (cleanupTrace archive digits suffix)
  rw [cleanup_length] at bound
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCleanup
