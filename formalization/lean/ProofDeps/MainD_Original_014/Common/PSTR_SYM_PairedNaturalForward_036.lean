module

public import Common.PSTR_SYM_PairedNaturalCode_035

/-! Actual return phase of the paired Natural compactor. It really crosses
each zero-lane/data pair and stops at the retained last TRUE flag, before
the arbitrary original suffix. Whole compaction still needs its backward
phase and original parsed entry; this local phase supplies neither by fiat. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive

open Turing PSTRTMSeq005

def forwardTrace (left : List Bool) : List Bool → List Bool → List (MachineState 11)
  | [], suffix => [state 8 left (true :: false :: suffix),
      state 10 (true :: left) (false :: suffix), state 11 (false :: true :: left) suffix]
  | bit :: later, suffix =>
      [state 8 left (false :: bit :: (naturalWord later ++ suffix)),
        state 9 (false :: left) (bit :: (naturalWord later ++ suffix))] ++
        forwardTrace (bit :: false :: left) later suffix

def forwardFinal (left digits suffix : List Bool) : MachineState 11 :=
  state 11 ((naturalWord digits).reverse ++ left) suffix

theorem forward_head (left digits suffix : List Bool) :
    (forwardTrace left digits suffix).head? = some (state 8 left (naturalWord digits ++ suffix)) := by
  cases digits with
  | nil => rfl
  | cons bit later =>
    simp only [forwardTrace, naturalWord_cons, List.cons_append, List.head?_cons]

theorem forward_last (left digits suffix : List Bool) :
    (forwardTrace left digits suffix).getLast? = some (forwardFinal left digits suffix) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [forwardTrace, List.getLast?_cons, ih, Option.getD_some, forwardFinal,
      naturalWord_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem forward_chain (left digits suffix : List Bool) :
    (forwardTrace left digits suffix).IsChain
      (fun before after => TM0.step naturalCompactMachine before = some after) := by
  induction digits generalizing left with
  | nil =>
    simp [forwardTrace, List.isChain_cons_cons, TM0.step, naturalCompactMachine, state, Tape.mk₂]
  | cons bit later ih =>
    apply List.IsChain.append
    · simp [List.isChain_cons_cons, TM0.step, naturalCompactMachine, state, Tape.mk₂]
    · exact ih _
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      rw [forward_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      simp [TM0.step, naturalCompactMachine, state, Tape.mk₂]

theorem forward_runsFrom (left digits suffix : List Bool) :
    RunsFrom naturalCompactMachine (state 8 left (naturalWord digits ++ suffix))
      (forwardTrace left digits suffix) (forwardFinal left digits suffix) :=
  ⟨forward_head left digits suffix, forward_chain left digits suffix,
    forward_last left digits suffix, naturalCompact_halt _ _⟩

theorem forward_length (left digits suffix : List Bool) :
    (forwardTrace left digits suffix).length = 2 * digits.length + 3 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [forwardTrace, List.length_append, List.length_cons, List.length_nil, ih]
    omega

def finishTrace (archive : List Bool) (first : Bool) (later suffix : List Bool) :
    List (MachineState 11) :=
  [state 4 archive (naturalWord (first :: later) ++ suffix),
    state 7 (false :: archive) (first :: (naturalWord later ++ suffix))] ++
    forwardTrace (first :: false :: archive) later suffix

theorem finish_runsFrom (archive : List Bool) (first : Bool) (later suffix : List Bool) :
    RunsFrom naturalCompactMachine (state 4 archive (naturalWord (first :: later) ++ suffix))
      (finishTrace archive first later suffix)
      (forwardFinal archive (first :: later) suffix) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply List.IsChain.append
    · simp [List.isChain_cons_cons, naturalWord_cons, TM0.step, naturalCompactMachine, state, Tape.mk₂]
    · exact forward_chain _ _ _
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      rw [forward_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      simp [TM0.step, naturalCompactMachine, state, Tape.mk₂]
  · simp only [finishTrace, List.getLast?_cons, forward_last, Option.getD_some,
      forwardFinal, naturalWord_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append]
  · exact naturalCompact_halt _ _

theorem finish_length (archive : List Bool) (first : Bool) (later suffix : List Bool) :
    (finishTrace archive first later suffix).length = 2 * later.length + 5 := by
  simp only [finishTrace, List.length_append, List.length_cons, List.length_nil, forward_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive
