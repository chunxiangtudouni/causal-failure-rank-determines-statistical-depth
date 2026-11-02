module

public import Common.PSTR_SYM_CountHeader_010

/-! Actual backward cleanup of one parsed Natural field. The current
suffix cell is never read or changed. A genuine FALSE Natural tag stops
the eraser; this is a structured field guard, not a blank-as-EOF test.
Returning across the cleared field is a separate actual program obligation. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicErase

open Turing PSTRTMRawNat010 PSTRTMSeq005

/-- Six fixed labels, before every field length, value, archive and suffix. -/
def backwardMachine : Machine 5 := fun label symbol =>
  match label.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .move .left)
  | 2 => if symbol then some (3, .write false) else none
  | 3 => some (4, .move .left)
  | 4 => some (5, .write false)
  | _ => some (2, .move .left)

def state (label : Fin 6) (left right : List Bool) : MachineState 5 :=
  ⟨label, Tape.mk₂ left right⟩

def coreTrace (archive cleared : List Bool) : List Bool → List (MachineState 5)
  | [] => [state 2 archive (false :: cleared)]
  | bit :: later =>
    [state 2 (bit :: (leftBlocks later ++ false :: archive)) (true :: cleared),
      state 3 (bit :: (leftBlocks later ++ false :: archive)) (false :: cleared),
      state 4 (leftBlocks later ++ false :: archive) (bit :: false :: cleared),
      state 5 (leftBlocks later ++ false :: archive) (false :: false :: cleared)] ++
      coreTrace archive (false :: false :: cleared) later

theorem core_head (archive cleared digits : List Bool) :
    (coreTrace archive cleared digits).head? = some
      (state 2 (leftBlocks digits ++ false :: archive).tail
        ((leftBlocks digits ++ false :: archive).headI :: cleared)) := by
  cases digits <;> rfl

theorem zeros_two (count : Nat) (right : List Bool) :
    List.replicate count false ++ false :: false :: right =
      List.replicate (count + 2) false ++ right := by
  rw [List.replicate_add]
  simp [List.replicate_succ, List.append_assoc]

theorem core_last (archive cleared digits : List Bool) :
    (coreTrace archive cleared digits).getLast? = some
      (state 2 archive (false :: (List.replicate (2 * digits.length) false ++ cleared))) := by
  induction digits generalizing cleared with
  | nil => rfl
  | cons bit later ih =>
    rw [coreTrace, List.getLast?_append, ih, Option.some_or]
    simp only [List.length_cons]
    rw [zeros_two]
    rw [show 2 * later.length + 2 = 2 * (later.length + 1) by omega]

theorem core_chain (archive cleared digits : List Bool) :
    (coreTrace archive cleared digits).IsChain
      (fun before after => TM0.step backwardMachine before = some after) := by
  induction digits generalizing cleared with
  | nil => exact .singleton _
  | cons bit later ih =>
    let front :=
      [state 2 (bit :: (leftBlocks later ++ false :: archive)) (true :: cleared),
        state 3 (bit :: (leftBlocks later ++ false :: archive)) (false :: cleared),
        state 4 (leftBlocks later ++ false :: archive) (bit :: false :: cleared),
        state 5 (leftBlocks later ++ false :: archive) (false :: false :: cleared)]
    have chain : front.IsChain (fun before after => TM0.step backwardMachine before = some after) := by
      simp [front, List.isChain_cons_cons, TM0.step, backwardMachine, state, Tape.mk₂]
    change (front ++ coreTrace archive (false :: false :: cleared) later).IsChain _
    apply chain.append (ih _)
    intro before beforeLast after afterHead
    have last : front.getLast? = some
        (state 5 (leftBlocks later ++ false :: archive) (false :: false :: cleared)) := rfl
    rw [last] at beforeLast
    rw [core_head] at afterHead
    simp only [Option.mem_some_iff] at beforeLast afterHead
    subst before
    subst after
    cases later <;> simp [TM0.step, backwardMachine, state, Tape.mk₂, leftBlocks]

theorem core_length (archive cleared digits : List Bool) :
    (coreTrace archive cleared digits).length = 4 * digits.length + 1 := by
  induction digits generalizing cleared with
  | nil => rfl
  | cons bit later ih =>
    rw [coreTrace, List.length_append, ih]
    simp only [List.length_cons, List.length_nil]
    omega

def backwardTrace (archive digits suffix : List Bool) : List (MachineState 5) :=
  [state 0 (false :: (leftBlocks digits.reverse ++ false :: archive)) suffix,
    state 1 (leftBlocks digits.reverse ++ false :: archive) (false :: suffix)] ++
      coreTrace archive (false :: suffix) digits.reverse

def backwardFinal (archive digits suffix : List Bool) : MachineState 5 :=
  state 2 archive (false :: (List.replicate (2 * digits.length + 1) false ++ suffix))

/-- A parsed field is actually erased all the way back to its original
Natural tag. The old current tag/suffix remains at its physical position. -/
theorem backward_runsFrom (archive digits suffix : List Bool) :
    RunsFrom backwardMachine
      (state 0 (false :: (leftBlocks digits.reverse ++ false :: archive)) suffix)
      (backwardTrace archive digits suffix) (backwardFinal archive digits suffix) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · let front :=
      [state 0 (false :: (leftBlocks digits.reverse ++ false :: archive)) suffix,
        state 1 (leftBlocks digits.reverse ++ false :: archive) (false :: suffix)]
    have chain : front.IsChain (fun before after => TM0.step backwardMachine before = some after) := by
      simp [front, List.isChain_cons_cons, TM0.step, backwardMachine, state, Tape.mk₂]
    change (front ++ coreTrace archive (false :: suffix) digits.reverse).IsChain _
    apply chain.append (core_chain archive (false :: suffix) digits.reverse)
    intro before beforeLast after afterHead
    have last : front.getLast? = some
        (state 1 (leftBlocks digits.reverse ++ false :: archive) (false :: suffix)) := rfl
    rw [last] at beforeLast
    rw [core_head] at afterHead
    simp only [Option.mem_some_iff] at beforeLast afterHead
    subst before
    subst after
    cases digits.reverse <;> simp [TM0.step, backwardMachine, state, Tape.mk₂, leftBlocks]
  · rw [backwardTrace, List.getLast?_append, core_last, Option.some_or]
    simp only [List.length_reverse]
    have zeros : List.replicate (2 * digits.length) false ++ false :: suffix =
        List.replicate (2 * digits.length + 1) false ++ suffix := by
      rw [List.replicate_add]
      simp [List.append_assoc]
    rw [zeros]
    rfl
  · simp [backwardFinal, state, TM0.step, backwardMachine, Tape.mk₂]

theorem backward_final_tape (archive digits suffix : List Bool) :
    (backwardFinal archive digits suffix).Tape =
      Tape.mk₂ archive (List.replicate (2 * digits.length + 2) false ++ suffix) := by
  change Tape.mk₂ archive (false :: (List.replicate (2 * digits.length + 1) false ++ suffix)) = _
  have cells : false :: (List.replicate (2 * digits.length + 1) false ++ suffix) =
      List.replicate (2 * digits.length + 2) false ++ suffix := by
    simp only [show 2 * digits.length + 2 = (2 * digits.length + 1) + 1 by omega,
      List.replicate_succ, List.cons_append]
  rw [cells]

theorem backward_length (archive digits suffix : List Bool) :
    (backwardTrace archive digits suffix).length = 4 * digits.length + 3 := by
  rw [backwardTrace, List.length_append, core_length, List.length_reverse]
  simp only [List.length_cons, List.length_nil]
  omega

theorem backward_space (archive digits suffix : List Bool) (inputLength : Nat) :
    visitedSpace backwardMachine inputLength (backwardTrace archive digits suffix) ≤
      inputLength + 8 * digits.length + 7 := by
  have bound := PSTRTMTrace002.visitedSpace_le backwardMachine inputLength
    (backwardTrace archive digits suffix)
  rw [backward_length] at bound
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicErase
