module

public import Common.PSTR_SYM_FieldCleanup_017

/-! One fixed tag-test/parser/END-marker-cleanup loop. Actual original
Natural fields are replaced by zero cells of the SAME physical length;
the next original tag, including EOF TRUE, is retained at its old position.
This is not yet an all-input symbolic serializer or a supplied field count. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalErase

open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002
open PSTRSymbolicLocator (naturalPrefix naturalPrefix_cons rawPayload_length)

def fieldMachine : Machine 27 := seqMachine streamMachine PSTRSymbolicCleanup.cleanupMachine

def erasedLeft (left : List Bool) (number : Nat) : List Bool :=
  List.replicate (2 * natBits number + 2) false ++ left

def fieldTrace (left : List Bool) (number : Nat) (suffix : List Bool) : List (MachineState 27) :=
  (streamTrace (false :: left) [] (PSTRTMNatValue017.rawPayload number) suffix).map (leftCfg (b := 9)) ++
    (PSTRSymbolicCleanup.cleanupTrace left (PSTRTMNatValue017.rawPayload number) suffix).map
      (rightCfg (a := 17))

def fieldFinal (left : List Bool) (number : Nat) (suffix : List Bool) : MachineState 27 :=
  rightCfg (a := 17) (PSTRSymbolicCleanup.cleanupFinal left (PSTRTMNatValue017.rawPayload number) suffix)

theorem field_runsFrom (left : List Bool) (number : Nat) (suffix : List Bool) :
    RunsFrom fieldMachine ⟨0, Tape.mk₂ (false :: left) (encodeNat number ++ suffix)⟩
      (fieldTrace left number suffix) (fieldFinal left number suffix) := by
  have parsed := encodeNat_stream_runsFrom (false :: left) suffix number
  have cleaned := PSTRSymbolicCleanup.cleanup_runsFrom left (PSTRTMNatValue017.rawPayload number) suffix
  have result := seq_runsFrom streamMachine PSTRSymbolicCleanup.cleanupMachine
    ⟨0, Tape.mk₂ (false :: left) (encodeNat number ++ suffix)⟩
    (streamFinal (false :: left) (PSTRTMNatValue017.rawPayload number) suffix)
    (PSTRSymbolicCleanup.cleanupFinal left (PSTRTMNatValue017.rawPayload number) suffix)
    (streamTrace (false :: left) [] (PSTRTMNatValue017.rawPayload number) suffix)
    (PSTRSymbolicCleanup.cleanupTrace left (PSTRTMNatValue017.rawPayload number) suffix) parsed cleaned
  simpa only [fieldMachine, fieldTrace, fieldFinal, leftCfg, leftLabel, Fin.val_zero, Fin.mk_zero]
    using result

theorem field_final_tape (left : List Bool) (number : Nat) (suffix : List Bool) :
    (fieldFinal left number suffix).Tape = Tape.mk₂ (erasedLeft left number) suffix := by
  simp only [fieldFinal, rightCfg, PSTRSymbolicCleanup.cleanup_final_tape, erasedLeft, rawPayload_length]

def embedLabel (label : Fin 28) : Fin 29 := ⟨label.val + 1, by omega⟩

def embed (before : MachineState 27) : MachineState 28 := ⟨embedLabel before.q, before.Tape⟩

def state (label : Fin 29) (left right : List Bool) : MachineState 28 := ⟨label, Tape.mk₂ left right⟩

/-- Twenty-nine fixed labels; the trace's Natural list is proof data only. -/
def eraseMachine : Machine 28 := fun label symbol =>
  if initial : label.val = 0 then
    if symbol then none else some (1, .move .right)
  else
    match fieldMachine ⟨label.val - 1, by omega⟩ symbol with
    | none => some (0, .write symbol)
    | some (next, instruction) => some (embedLabel next, instruction)

theorem erase_step_embed (before : MachineState 27) :
    TM0.step eraseMachine (embed before) =
      match TM0.step fieldMachine before with
      | none => some ⟨0, before.Tape⟩
      | some after => some (embed after) := by
  cases before with
  | mk label tape =>
    unfold TM0.step eraseMachine embed embedLabel
    simp only [show ¬ label.val + 1 = 0 by omega, ↓reduceDIte, Nat.add_sub_cancel, Fin.eta]
    cases action : fieldMachine label tape.head with
    | none => simp [Tape.write_self]
    | some pair =>
      obtain ⟨next, instruction⟩ := pair
      cases instruction <;> rfl

theorem erase_false_step (left right : List Bool) :
    TM0.step eraseMachine (state 0 left (false :: right)) =
      some (embed ⟨0, Tape.mk₂ (false :: left) right⟩) := by
  simp [TM0.step, eraseMachine, state, embed, embedLabel, Tape.mk₂]

theorem erase_true_halt (left right : List Bool) :
    TM0.step eraseMachine (state 0 left (true :: right)) = none := by
  simp [TM0.step, eraseMachine, state, Tape.mk₂]

def eraseArchive (left : List Bool) (numbers : List Nat) : List Bool := numbers.foldl erasedLeft left

def eraseTrace (left : List Bool) : List Nat → List Bool → List (MachineState 28)
  | [], suffix => [state 0 left (true :: suffix)]
  | number :: later, suffix =>
    state 0 left (naturalPrefix (number :: later) ++ true :: suffix) ::
      ((fieldTrace left number (naturalPrefix later ++ true :: suffix)).map embed ++
        eraseTrace (erasedLeft left number) later suffix)

def eraseFinal (left : List Bool) (numbers : List Nat) (suffix : List Bool) : MachineState 28 :=
  state 0 (eraseArchive left numbers) (true :: suffix)

theorem eraseArchive_exact (left : List Bool) (numbers : List Nat) :
    eraseArchive left numbers = List.replicate (naturalPrefix numbers).length false ++ left := by
  induction numbers generalizing left with
  | nil => rfl
  | cons number later ih =>
    change eraseArchive (erasedLeft left number) later = _
    rw [ih]
    simp only [erasedLeft, naturalPrefix_cons, List.length_append,
      PSTRTMLength004.encodeDatum_natural_length]
    rw [← List.append_assoc, ← List.replicate_add]
    simp only [Nat.add_comm]

theorem erase_final_tape (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    (eraseFinal left numbers suffix).Tape =
      Tape.mk₂ (List.replicate (naturalPrefix numbers).length false ++ left) (true :: suffix) := by
  simp only [eraseFinal, state, eraseArchive_exact]

theorem eraseTrace_head (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    (eraseTrace left numbers suffix).head? = some (state 0 left (naturalPrefix numbers ++ true :: suffix)) := by
  cases numbers <;> rfl

theorem eraseTrace_nonempty (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    eraseTrace left numbers suffix ≠ [] := by
  intro empty
  have head := eraseTrace_head left numbers suffix
  simp only [empty, List.head?_nil, reduceCtorEq] at head

theorem eraseTrace_last (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    (eraseTrace left numbers suffix).getLast? = some (eraseFinal left numbers suffix) := by
  induction numbers generalizing left with
  | nil => rfl
  | cons number later ih =>
    have nonempty := List.append_ne_nil_of_right_ne_nil
      ((fieldTrace left number (naturalPrefix later ++ true :: suffix)).map embed)
      (eraseTrace_nonempty (erasedLeft left number) later suffix)
    rw [eraseTrace, List.getLast?_cons_of_ne_nil nonempty, List.getLast?_append, ih, Option.some_or]
    rfl

theorem erase_runsFrom (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    RunsFrom eraseMachine (state 0 left (naturalPrefix numbers ++ true :: suffix))
      (eraseTrace left numbers suffix) (eraseFinal left numbers suffix) := by
  induction numbers generalizing left with
  | nil => exact ⟨rfl, .singleton _, rfl, erase_true_halt left suffix⟩
  | cons number later ih =>
    have field := field_runsFrom left number (naturalPrefix later ++ true :: suffix)
    have continuation := ih (erasedLeft left number)
    have fieldChain : ((fieldTrace left number (naturalPrefix later ++ true :: suffix)).map embed).IsChain
        (fun before after => TM0.step eraseMachine before = some after) := by
      apply (List.isChain_map _).mpr
      apply field.2.1.imp
      intro before after actual
      rw [erase_step_embed, actual]
    have joined := fieldChain.append continuation.2.1 (by
      intro before beforeLast after afterHead
      simp only [List.getLast?_map, field.2.2.1, Option.map_some, Option.mem_some_iff] at beforeLast
      simp only [eraseTrace_head, Option.mem_some_iff] at afterHead
      subst before
      subst after
      rw [erase_step_embed, field.2.2.2, field_final_tape]
      rfl)
    refine ⟨eraseTrace_head left (number :: later) suffix, ?_,
      eraseTrace_last left (number :: later) suffix, erase_true_halt _ _⟩
    change List.IsChain _ (state 0 left
      (encodeDatum (.natural number) ++ naturalPrefix later ++ true :: suffix) :: _)
    apply List.isChain_cons.mpr
    refine ⟨?_, joined⟩
    intro after afterHead
    simp only [List.head?_append, List.head?_map, field.1,
      Option.map_some, Option.some_or, Option.mem_some_iff] at afterHead
    subst after
    simpa only [encodeDatum, List.cons_append, List.append_assoc] using
      erase_false_step left (encodeNat number ++ naturalPrefix later ++ true :: suffix)

theorem erase_time_le (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    (eraseTrace left numbers suffix).length ≤ 32 * ((naturalPrefix numbers).length + 1)^2 := by
  induction numbers generalizing left with
  | nil => change 1 ≤ 32; decide
  | cons number later ih =>
    have previous := ih (erasedLeft left number)
    have count : (eraseTrace left (number :: later) suffix).length =
        (natBits number)^2 + 15 * natBits number + 10 +
          (eraseTrace (erasedLeft left number) later suffix).length := by
      simp only [eraseTrace, List.length_cons, List.length_append, List.length_map, fieldTrace,
        streamTrace_length, PSTRSymbolicCleanup.cleanup_length, rawPayload_length]
      omega
    have field : (naturalPrefix (number :: later)).length =
        2 * natBits number + 2 + (naturalPrefix later).length := by
      rw [naturalPrefix_cons, List.length_append, PSTRTMLength004.encodeDatum_natural_length]
    rw [count, field]
    nlinarith [Nat.zero_le ((naturalPrefix later).length * natBits number)]

theorem erase_space_le (inputLength : Nat) (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    visitedSpace eraseMachine inputLength (eraseTrace left numbers suffix) ≤
      inputLength + 64 * ((naturalPrefix numbers).length + 1)^2 + 1 := by
  have cells := PSTRTMTrace002.visitedSpace_le eraseMachine inputLength (eraseTrace left numbers suffix)
  have clock := erase_time_le left numbers suffix
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalErase
