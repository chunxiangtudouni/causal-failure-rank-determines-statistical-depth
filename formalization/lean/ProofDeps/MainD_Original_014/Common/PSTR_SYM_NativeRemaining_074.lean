module

public import Common.PSTR_SYM_RetainedBootstrapNative_073
public import Common.PSTR_SYM_RawLoopSuffix_067

/-! The actual remaining-list loop at its real internal native label,
including the paid cursor return to its genuine terminal CFG. This is
not a reset to rawLoopMachine's original control0/bootstrap. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNativeRemaining

open Turing PSTRTMSeq005 PSTRSymbolicRelabel PSTRSymbolicRawLoop
open PSTRSymbolicRetainedBootstrap PSTRSymbolicLaneArchive PSTRSymbolicCursorArchive PSTRTMIncrement009

noncomputable def entryLabel : Fin (loopSupport.card + 1) :=
  (finiteLabels loopSupport) (LoopLabel.datum 0)

noncomputable def exitLabel : Fin (loopSupport.card + 1) :=
  (finiteLabels loopSupport) (LoopLabel.done true)

theorem actual_native_remaining (data remaining : List Datum) (base digits unread : List Bool) (bytes : Nat)
    (nonempty : remaining ≠ []) (archiveRoom : 3 ≤ (allDatumPairs data).length)
    (headerRoom : 3 ≤ digits.length) (countValue : valueDigits digits = remaining.length)
    (sized : ∀ value ∈ remaining, (encodeDatum value).length ≤ bytes) :
    ∃ (endDigits : List Bool) (trace : List (MachineState loopSupport.card)) (final : MachineState loopSupport.card),
      RunsFrom rawLoopMachine ⟨entryLabel,pendingSuffix data base digits remaining unread⟩ trace final ∧
      final.q = exitLabel ∧ final.Tape = archiveTape (data ++ remaining) base endDigits unread true ∧
      valueDigits endDigits = 0 ∧ endDigits.length = digits.length ∧
      trace.length ≤ remaining.length * cycleBudget (allDatumPairs (data ++ remaining)).length digits.length bytes + 1 ∧
      ∀ inputLength clock, visitedSpace rawLoopMachine inputLength (trace.take clock) ≤
        inputLength + 2 * (remaining.length * cycleBudget (allDatumPairs (data ++ remaining)).length digits.length bytes + 1) + 1 := by
  obtain ⟨endDigits,oldTrace,oldFinal,firstHead,chain,lastHead,_port,tape,next,value,width,time⟩ :=
    actual_remaining_suffix data remaining base digits unread bytes nonempty archiveRoom headerRoom countValue sized
  let sourceFinal : TM0.Cfg Bool LoopLabel := ⟨.done true,oldFinal.Tape⟩
  let sourceTrace := oldTrace ++ [sourceFinal]
  have sourceHead : sourceTrace.head? = some ⟨.datum 0,pendingSuffix data base digits remaining unread⟩ := by
    simp only [sourceTrace,List.head?_append,firstHead,Option.some_or]
  have sourceLast : sourceTrace.getLast? = some sourceFinal := by
    simp only [sourceTrace,List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have sourceChain : sourceTrace.IsChain (fun before after => TM0.step loopCode before = some after) := by
    apply List.IsChain.append chain (.singleton _)
    intro before beforeLast after afterHead
    simp only [lastHead,Option.mem_some_iff] at beforeLast
    simp only [List.head?_cons,Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact next
  let trace := sourceTrace.map (relabelCfg (finiteLabels loopSupport))
  let final := relabelCfg (finiteLabels loopSupport) sourceFinal
  have actual := finite_from_univ loopCode
    ⟨.datum 0,pendingSuffix data base digits remaining unread⟩ sourceFinal sourceTrace
    sourceHead sourceChain sourceLast (loop_halt true _)
  have finalTape : final.Tape = archiveTape (data ++ remaining) base endDigits unread true := tape
  have length : trace.length = oldTrace.length + 1 := by
    simp only [trace,sourceTrace,List.length_map,List.length_append,List.length_singleton]
  refine ⟨endDigits,trace,final,actual,rfl,finalTape,value,width,?_,?_⟩
  · rw [length]
    omega
  · intro inputLength clock
    have cells := PSTRTMTrace002.visitedSpace_le rawLoopMachine inputLength (trace.take clock)
    have takeLength : (trace.take clock).length ≤ oldTrace.length + 1 := by
      simp only [List.length_take,length]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNativeRemaining
