module

public import Structure.PA17_TM_Division_Loop_002e

/-! Actual commit: find the same pending source cell, write the finite
control's quotient bit, clear that cell's pending flag, and physically
return to resident. All other cells, including both flags, are preserved. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
open PSTRTMCompareCode054 PSTRTMBinaryAdd024

def commitMode : List (Bool × Bool) → Fin 3
  | [] => 0
  | (_,false) :: lower => commitMode lower
  | (_,true) :: _ => 1

def commitMSB (emit : Bool) : List (Bool × Bool) → List (Bool × Bool)
  | [] => []
  | (a,false) :: lower => (a,false) :: commitMSB emit lower
  | (_,true) :: lower => (emit,false) :: lower

theorem commitMSB_length (emit : Bool) (pairs : List (Bool × Bool)) :
    (commitMSB emit pairs).length = pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair lower ih => rcases pair with ⟨a,p⟩; cases p <;> simp [commitMSB, ih]

def commitWriteTrace (emit : Bool) (left right : List Bool) : List (MachineState 33) :=
  [commitState 28 left (emit :: true :: true :: true :: right),
   commitState 29 (emit :: left) (true :: true :: true :: right),
   commitState 30 (true :: emit :: left) (true :: true :: right),
   commitState 31 (true :: emit :: left) (false :: true :: right),
   commitState 32 (emit :: left) (true :: false :: true :: right),
   commitState 33 left (emit :: true :: false :: true :: right)]

theorem commit_write_head (emit : Bool) (left right : List Bool) :
    (commitWriteTrace emit left right).head? = some (commitState 28 left (emit :: true :: true :: true :: right)) := rfl

theorem commit_write_last (emit : Bool) (left right : List Bool) :
    (commitWriteTrace emit left right).getLast? = some (commitState 33 left (emit :: true :: false :: true :: right)) := rfl

theorem commit_write_chain (emit : Bool) (left right : List Bool) :
    (commitWriteTrace emit left right).IsChain (fun before after => Turing.TM0.step (commitMachine emit) before = some after) := by
  simp [commitWriteTrace, List.isChain_cons_cons, Turing.TM0.step, commitMachine, commitState, Turing.Tape.mk₂]

theorem commit_skip_chain (emit a : Bool) (left right : List Bool) :
    ((skipSourceTrace a left right).map commitCfg).IsChain
      (fun before after => Turing.TM0.step (commitMachine emit) before = some after) := by
  simp [skipSourceTrace, List.isChain_cons_cons, Turing.TM0.step, commitMachine, commitCfg,
    commitLabel, sourceState, sourceMachine, Turing.Tape.mk₂]

theorem commit_found_chain (emit a : Bool) (left right : List Bool) :
    ((foundSourceTrace a left right).map commitCfg).IsChain
      (fun before after => Turing.TM0.step (commitMachine emit) before = some after) := by
  simp [foundSourceTrace, List.isChain_cons_cons, Turing.TM0.step, commitMachine, commitCfg,
    commitLabel, sourceState, sourceMachine, Turing.Tape.mk₂]

def commitScanTrace (emit : Bool) (context : List Bool) :
    List (Bool × Bool) → List (Bool × Bool) → List Bool → List (MachineState 33)
  | [], higher, resident =>
    [commitCfg (sourceState 4 context (false :: (operandColumns higher ++ false :: false :: false :: resident)))] ++
      commitReturnTrace 0 (false :: context) [] higher resident
  | (a,false) :: lower, higher, resident =>
    (skipSourceTrace a (leftColumns lower ++ false :: context)
      (operandColumns higher ++ false :: false :: false :: resident)).map commitCfg ++
      commitScanTrace emit context lower ((a,false) :: higher) resident
  | (a,true) :: lower, higher, resident =>
    (foundSourceTrace a (leftColumns lower ++ false :: context)
      (operandColumns higher ++ false :: false :: false :: resident)).map commitCfg ++
      commitWriteTrace emit (leftColumns lower ++ false :: context)
        (operandColumns higher ++ false :: false :: false :: resident) ++
      commitReturnTrace 1 (leftColumns lower ++ false :: context) [] ((emit,false) :: higher) resident

theorem commit_scan_head (emit : Bool) (context : List Bool) (remaining higher : List (Bool × Bool)) (resident : List Bool) :
    (commitScanTrace emit context remaining higher resident).head? = some (commitCfg (scanInitial context remaining higher resident)) := by
  cases remaining with
  | nil => rfl
  | cons pair lower =>
    rcases pair with ⟨a,p⟩
    cases p <;> simp [commitScanTrace, scanInitial, List.head?_append, skip_source_head, found_source_head]

theorem commit_scan_last (emit : Bool) (context : List Bool) (remaining higher : List (Bool × Bool)) (resident : List Bool) :
    (commitScanTrace emit context remaining higher resident).getLast? = some
      (commitState (commitLabel (sourceHalt (commitMode remaining)))
        (false :: false :: false :: (leftColumns (higher.reverse ++ commitMSB emit remaining) ++ false :: context)) resident) := by
  induction remaining generalizing higher with
  | nil =>
    have hne : commitReturnTrace 0 (false :: context) [] higher resident ≠ [] := by
      intro he
      have hl := commit_return_length 0 (false :: context) [] higher resident
      simp [he] at hl
    change (_ :: commitReturnTrace 0 (false :: context) [] higher resident).getLast? = _
    rw [List.getLast?_cons_of_ne_nil hne, commit_return_last]
    simp only [commitMode, commitMSB, List.append_nil]
  | cons pair lower ih =>
    rcases pair with ⟨a,p⟩
    cases p with
    | false =>
      simp [commitScanTrace, List.getLast?_append, ih, commitMode, commitMSB,
        List.reverse_cons, List.append_assoc]
    | true =>
      simp [commitScanTrace, List.getLast?_append, commit_return_last, commitMode, commitMSB,
        List.reverse_cons, leftColumns, List.flatMap_append, List.append_assoc]

theorem commit_scan_length_le (emit : Bool) (context : List Bool) (remaining higher : List (Bool × Bool)) (resident : List Bool) :
    (commitScanTrace emit context remaining higher resident).length ≤ 8 * remaining.length + 4 * higher.length + 11 := by
  induction remaining generalizing higher with
  | nil =>
    simp only [commitScanTrace, List.length_append, List.length_cons, List.length_nil, commit_return_length]
    omega
  | cons pair lower ih =>
    rcases pair with ⟨a,p⟩
    cases p with
    | false =>
      have hs := ih ((a,false) :: higher)
      simp only [commitScanTrace, List.length_append, List.length_map, skipSourceTrace, List.length_cons, List.length_nil] at hs ⊢
      omega
    | true =>
      simp only [commitScanTrace, List.length_append, List.length_map, foundSourceTrace, commitWriteTrace,
        List.length_cons, List.length_nil, commit_return_length]
      omega

theorem commit_scan_chain (emit : Bool) (context : List Bool) (remaining higher : List (Bool × Bool)) (resident : List Bool) :
    (commitScanTrace emit context remaining higher resident).IsChain
      (fun before after => Turing.TM0.step (commitMachine emit) before = some after) := by
  induction remaining generalizing higher with
  | nil =>
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      change after ∈ (commitReturnTrace 0 (false :: context) [] higher resident).head? at ha
      rw [commit_return_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      simp [Turing.TM0.step, commitMachine, commitCfg, commitLabel, commitState, sourceState,
        sourceMachine, returnSource, returnLabel, Turing.Tape.mk₂, leftColumns]
    · exact commit_return_chain emit 0 (false :: context) [] higher resident
  | cons pair lower ih =>
    rcases pair with ⟨a,p⟩
    cases p with
    | false =>
      rw [commitScanTrace]
      apply (commit_skip_chain emit a _ _).append (ih ((a,false) :: higher))
      intro before hb after ha
      simp only [List.getLast?_map, skip_source_last, Option.map_some, Option.mem_some_iff] at hb
      simp only [commit_scan_head, Option.mem_some_iff] at ha
      subst before
      subst after
      cases lower with
      | nil => simp [scanInitial, Turing.TM0.step, commitMachine, commitCfg, commitLabel, sourceState,
          sourceMachine, leftColumns, operandColumns, Turing.Tape.mk₂]
      | cons pair rest =>
        rcases pair with ⟨b,p⟩
        simp [scanInitial, Turing.TM0.step, commitMachine, commitCfg, commitLabel, sourceState,
          sourceMachine, leftColumns, operandColumns, Turing.Tape.mk₂]
    | true =>
      rw [commitScanTrace]
      apply List.IsChain.append
      · apply (commit_found_chain emit a _ _).append (commit_write_chain emit _ _)
        intro before hb after ha
        simp only [List.getLast?_map, found_source_last, Option.map_some, Option.mem_some_iff] at hb
        simp only [commit_write_head, Option.mem_some_iff] at ha
        subst before
        subst after
        simp [Turing.TM0.step, commitMachine, commitCfg, commitLabel, commitState, sourceState, Turing.Tape.mk₂]
      · exact commit_return_chain emit 1 _ [] ((emit,false) :: higher) resident
      · intro before hb after ha
        simp only [List.getLast?_append, commit_write_last, Option.some_or, Option.mem_some_iff] at hb
        simp only [commit_return_head, Option.mem_some_iff] at ha
        subst before
        subst after
        simp [Turing.TM0.step, commitMachine, commitLabel, commitState, returnSource, returnLabel,
          leftColumns, operandColumns, Turing.Tape.mk₂]

def commitTrace (emit : Bool) (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) : List (MachineState 33) :=
  (startupTrace context archive resident).map commitCfg ++ commitScanTrace emit context archive.reverse [] resident

theorem commit_head (emit : Bool) (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    (commitTrace emit context archive resident).head? = some
      (commitState 0 (false :: false :: false :: (leftColumns archive.reverse ++ false :: context)) resident) := by
  simp [commitTrace, startupTrace, commitCfg, commitState, commitLabel, sourceState]

theorem commit_last (emit : Bool) (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    (commitTrace emit context archive resident).getLast? = some
      (commitState (commitLabel (sourceHalt (commitMode archive.reverse)))
        (false :: false :: false :: (leftColumns (commitMSB emit archive.reverse) ++ false :: context)) resident) := by
  simp [commitTrace, List.getLast?_append, commit_scan_last]

theorem commit_length_le (emit : Bool) (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    (commitTrace emit context archive resident).length ≤ 8 * archive.length + 15 := by
  have hs := commit_scan_length_le emit context archive.reverse [] resident
  simp only [commitTrace, List.length_append, List.length_map, startupTrace, List.length_cons, List.length_nil,
    List.length_reverse] at hs ⊢
  omega

theorem commit_chain (emit : Bool) (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    (commitTrace emit context archive resident).IsChain
      (fun before after => Turing.TM0.step (commitMachine emit) before = some after) := by
  apply List.IsChain.append
  · simp [startupTrace, List.isChain_cons_cons, Turing.TM0.step, commitMachine, commitCfg, commitLabel,
      sourceState, sourceMachine, Turing.Tape.mk₂]
  · exact commit_scan_chain emit context archive.reverse [] resident
  · intro before hb after ha
    simp [startupTrace] at hb
    simp only [commit_scan_head, Option.mem_some_iff] at ha
    subst before
    subst after
    generalize he : archive.reverse = remaining
    cases remaining with
    | nil => simp [scanInitial, Turing.TM0.step, commitMachine, commitCfg, commitLabel, sourceState,
        sourceMachine, leftColumns, operandColumns, Turing.Tape.mk₂]
    | cons pair lower =>
      rcases pair with ⟨a,p⟩
      simp [scanInitial, Turing.TM0.step, commitMachine, commitCfg, commitLabel, sourceState,
        sourceMachine, leftColumns, operandColumns, Turing.Tape.mk₂]

theorem commit_runsFrom (emit : Bool) (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    PSTRTMSeq005.RunsFrom (commitMachine emit)
      (commitState 0 (false :: false :: false :: (leftColumns archive.reverse ++ false :: context)) resident)
      (commitTrace emit context archive resident)
      (commitState (commitLabel (sourceHalt (commitMode archive.reverse)))
        (false :: false :: false :: (leftColumns (commitMSB emit archive.reverse) ++ false :: context)) resident) :=
  ⟨commit_head emit context archive resident, commit_chain emit context archive resident,
    commit_last emit context archive resident, commit_halt emit _ _ _⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
