module

public import Common.PSTR_SYM_FirstNatBranch_027

/-! The two statically installed callees are reached only after the actual
outer count has been restored. Original input parsing, N testing, rewind,
unblocking and the callee all lie on ONE charged finite-control trace. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicFront

open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002
open PSTRSymbolicLocator (outerLeft)

variable {a : Nat}

def restoreThenMachine (callee : Machine a) : Machine (25 + a + 1) :=
  seqMachine restoreCountMachine callee

def restoreThenTrace (count : Nat) (suffix : List Bool) (trace : List (MachineState a)) :
    List (MachineState (25 + a + 1)) :=
  (restoreCountTrace count suffix).map (leftCfg (b := a)) ++ trace.map (rightCfg (a := 25))

theorem restoreThen_runsFrom (callee : Machine a) (count : Nat) (suffix : List Bool)
    (trace : List (MachineState a)) (final : MachineState a)
    (run : RunsFrom callee ⟨0, Tape.mk₁ (encodeNat count ++ false :: suffix)⟩ trace final) :
    RunsFrom (restoreThenMachine callee) ⟨0, Tape.mk₂ (outerLeft [] count) (false :: suffix)⟩
      (restoreThenTrace count suffix trace) (rightCfg (a := 25) final) := by
  apply seq_runsFrom restoreCountMachine callee
    ⟨0, Tape.mk₂ (outerLeft [] count) (false :: suffix)⟩
    (restoreCountFinal count suffix) final (restoreCountTrace count suffix) trace
  · exact restoreCount_runsFrom count suffix
  · rw [restoreCount_final_tape]
    exact run

abbrev zeroRestoreCap : Nat := 25 + 173 + 1
abbrev priorRestoreCap : Nat := 25 + 82 + 1
abbrev selectCap : Nat := zeroRestoreCap + priorRestoreCap + 12
abbrev frontCap : Nat := 17 + selectCap + 1

def zeroRestoreMachine : Machine zeroRestoreCap :=
  restoreThenMachine PSTRSymbolicZeroTail.zeroSymbolicMachine

def priorRestoreMachine : Machine priorRestoreCap :=
  restoreThenMachine PSTRSymbolicLocator.firstRatMachine

def selectMachine : Machine selectCap := firstNatBranchMachine zeroRestoreMachine priorRestoreMachine

def symbolicFrontMachine : Machine frontCap := seqMachine streamMachine selectMachine

theorem symbolicFrontMachine_labels : frontCap + 1 = 338 := by decide

/-- The actual zero port of the one fixed front program. The callee run
is an internal compositional premise on the restored ORIGINAL input. -/
theorem front_zero_runsFrom (count : Nat) (suffix : List Bool)
    (trace : List (MachineState 173)) (final : MachineState 173)
    (run : RunsFrom PSTRSymbolicZeroTail.zeroSymbolicMachine
      ⟨0, Tape.mk₁ (encodeNat count ++ encodeDatum (.natural 0) ++ suffix)⟩ trace final) :
    ∃ (wholeTrace : List (MachineState frontCap)) (wholeFinal : MachineState frontCap),
      RunsFrom symbolicFrontMachine
        ⟨0, Tape.mk₁ (encodeNat count ++ encodeDatum (.natural 0) ++ suffix)⟩ wholeTrace wholeFinal ∧
      wholeFinal.Tape = final.Tape ∧
      wholeTrace.length ≤ 48 * (natBits count + 1)^2 + 7 + trace.length := by
  let rest := encodeNat 0 ++ suffix
  obtain ⟨testTrace, testRun, testTime, _testSpace⟩ :=
    firstNat_runsFrom (outerLeft [] count) 0 suffix
  let restoredTrace := restoreThenTrace count rest trace
  let restoredFinal : MachineState zeroRestoreCap := rightCfg (a := 25) final
  have restoreRun : RunsFrom zeroRestoreMachine
      ⟨0, Tape.mk₂ (outerLeft [] count) (encodeDatum (.natural 0) ++ suffix)⟩
      restoredTrace restoredFinal := restoreThen_runsFrom _ count rest trace final (by
        rw [List.append_assoc] at run
        exact run)
  have selected := branch_runs_zero zeroRestoreMachine priorRestoreMachine
    (state 0 (outerLeft [] count) (encodeDatum (.natural 0) ++ suffix))
    (state 10 (outerLeft [] count) (encodeDatum (.natural 0) ++ suffix))
    restoredFinal testTrace restoredTrace testRun rfl restoreRun
  let selectedTrace := testTrace.map (testCfg (z := zeroRestoreCap) (p := priorRestoreCap)) ++
    restoredTrace.map (zeroCfg (p := priorRestoreCap))
  let selectedFinal : MachineState selectCap := zeroCfg restoredFinal
  let headerTrace := streamTrace [] [] (PSTRTMNatValue017.rawPayload count)
    (encodeDatum (.natural 0) ++ suffix)
  let wholeTrace := headerTrace.map (leftCfg (b := selectCap)) ++
    selectedTrace.map (rightCfg (a := 17))
  let wholeFinal : MachineState frontCap := rightCfg (a := 17) selectedFinal
  refine ⟨wholeTrace, wholeFinal, ?_, rfl, ?_⟩
  · apply seq_runsFrom streamMachine selectMachine
      ⟨0, Tape.mk₁ (encodeNat count ++ encodeDatum (.natural 0) ++ suffix)⟩
      (streamFinal [] (PSTRTMNatValue017.rawPayload count) (encodeDatum (.natural 0) ++ suffix))
      selectedFinal headerTrace selectedTrace
    · have entry : streamState 0 [] (encodeNat count ++ (encodeDatum (.natural 0) ++ suffix)) =
          (⟨0, Tape.mk₁ (encodeNat count ++ encodeDatum (.natural 0) ++ suffix)⟩ : MachineState 17) := by
        simp only [streamState, Tape.mk₁, List.append_assoc]
      have actual := encodeNat_stream_runsFrom [] (encodeDatum (.natural 0) ++ suffix) count
      rw [entry] at actual
      exact actual
    · exact selected
  · have headerTime := stream_length_le [] (PSTRTMNatValue017.rawPayload count)
      (encodeDatum (.natural 0) ++ suffix)
    rw [PSTRSymbolicLocator.rawPayload_length] at headerTime
    have restoreTime := restoreCount_time_le count rest
    simp only [wholeTrace, headerTrace, selectedTrace, restoredTrace, restoreThenTrace,
      List.length_append, List.length_map]
    omega

/-- The actual positive port; the installed callee stages the first prior.
It deliberately does not claim the positive symbolic output is finished. -/
theorem front_positive_runsFrom (count number : Nat) (suffix : List Bool) (positive : 0 < number)
    (trace : List (MachineState 82)) (final : MachineState 82)
    (run : RunsFrom PSTRSymbolicLocator.firstRatMachine
      ⟨0, Tape.mk₁ (encodeNat count ++ encodeDatum (.natural number) ++ suffix)⟩ trace final) :
    ∃ (wholeTrace : List (MachineState frontCap)) (wholeFinal : MachineState frontCap),
      RunsFrom symbolicFrontMachine
        ⟨0, Tape.mk₁ (encodeNat count ++ encodeDatum (.natural number) ++ suffix)⟩ wholeTrace wholeFinal ∧
      wholeFinal.Tape = final.Tape ∧
      wholeTrace.length ≤ 48 * (natBits count + 1)^2 + 7 + trace.length := by
  let rest := encodeNat number ++ suffix
  have nonzero : number ≠ 0 := by omega
  obtain ⟨testTrace, testRun, testTime, _testSpace⟩ :=
    firstNat_runsFrom (outerLeft [] count) number suffix
  simp only [nonzero, ite_false] at testRun
  let restoredTrace := restoreThenTrace count rest trace
  let restoredFinal : MachineState priorRestoreCap := rightCfg (a := 25) final
  have restoreRun : RunsFrom priorRestoreMachine
      ⟨0, Tape.mk₂ (outerLeft [] count) (encodeDatum (.natural number) ++ suffix)⟩
      restoredTrace restoredFinal := restoreThen_runsFrom _ count rest trace final (by
        rw [List.append_assoc] at run
        exact run)
  have selected := branch_runs_positive zeroRestoreMachine priorRestoreMachine
    (state 0 (outerLeft [] count) (encodeDatum (.natural number) ++ suffix))
    (state 5 (outerLeft [] count) (encodeDatum (.natural number) ++ suffix))
    restoredFinal testTrace restoredTrace testRun (by decide : (5 : Nat) ≠ 10) restoreRun
  let selectedTrace := testTrace.map (testCfg (z := zeroRestoreCap) (p := priorRestoreCap)) ++
    restoredTrace.map (positiveCfg (z := zeroRestoreCap))
  let selectedFinal : MachineState selectCap := positiveCfg restoredFinal
  let headerTrace := streamTrace [] [] (PSTRTMNatValue017.rawPayload count)
    (encodeDatum (.natural number) ++ suffix)
  let wholeTrace := headerTrace.map (leftCfg (b := selectCap)) ++
    selectedTrace.map (rightCfg (a := 17))
  let wholeFinal : MachineState frontCap := rightCfg (a := 17) selectedFinal
  refine ⟨wholeTrace, wholeFinal, ?_, rfl, ?_⟩
  · apply seq_runsFrom streamMachine selectMachine
      ⟨0, Tape.mk₁ (encodeNat count ++ encodeDatum (.natural number) ++ suffix)⟩
      (streamFinal [] (PSTRTMNatValue017.rawPayload count) (encodeDatum (.natural number) ++ suffix))
      selectedFinal headerTrace selectedTrace
    · have entry : streamState 0 [] (encodeNat count ++ (encodeDatum (.natural number) ++ suffix)) =
          (⟨0, Tape.mk₁ (encodeNat count ++ encodeDatum (.natural number) ++ suffix)⟩ : MachineState 17) := by
        simp only [streamState, Tape.mk₁, List.append_assoc]
      have actual := encodeNat_stream_runsFrom [] (encodeDatum (.natural number) ++ suffix) count
      rw [entry] at actual
      exact actual
    · exact selected
  · have headerTime := stream_length_le [] (PSTRTMNatValue017.rawPayload count)
      (encodeDatum (.natural number) ++ suffix)
    rw [PSTRSymbolicLocator.rawPayload_length] at headerTime
    have restoreTime := restoreCount_time_le count rest
    simp only [wholeTrace, headerTrace, selectedTrace, restoredTrace, restoreThenTrace,
      List.length_append, List.length_map]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicFront
