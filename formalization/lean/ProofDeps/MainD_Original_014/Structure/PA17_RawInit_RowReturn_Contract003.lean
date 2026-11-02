module
public import Structure.PA17_RawInit_RowReturn_Trace002

/-! One fixed machine, entry and genuine HALT before all row bits, gap,
arbitrary left/suffix and original inputLength. No host count enters code. -/
@[expose] public section
namespace PaperProofs.Common.Native.PA17RawInitRowReturn
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

theorem rows_length (bits : List Bool) : (rows bits).length=33*(bits.length+1) := by
  simp only [rows,List.length_append,PSTRWordBool.RawInit.rowBits_length,PSTRWordBool.RawInit.rows_length]
  omega

theorem return_contract (bits : List Bool) (gap : Nat) (left suffix : List Bool) (inputLength : Nat) :
    ∃ trace,RunsFrom machine (state 0 (initialTape bits gap left suffix)) trace
      (state 34 (finalTape bits gap left suffix)) ∧
      trace.length ≤ 3*((rows bits).length+gap+1) ∧ ∀ clock,
      visitedSpace machine inputLength (trace.take clock) ≤ inputLength+6*((rows bits).length+gap+1)+1 := by
  obtain ⟨trace,run,length⟩:=rows_run bits gap left suffix
  have width:=rows_length bits
  have time : trace.length ≤ 3*((rows bits).length+gap+1) := by omega
  refine ⟨trace,run,time,?_⟩
  intro clock
  have space:=PSTRTMTrace002.visitedSpace_le machine inputLength (trace.take clock)
  have take:=(List.length_take_le' clock trace).trans time
  omega

theorem fixed_machine :
    ∃ (states timeCoefficient spaceCoefficient : Nat) (program : Machine states) (halt : Fin (states+1)),
      0<timeCoefficient ∧ 0<spaceCoefficient ∧
      ∀ (bits : List Bool) (gap : Nat) (left suffix : List Bool) (inputLength : Nat),
      let rowWord:=PSTRWordBool.RawInit.rowBits true true++bits.flatMap (PSTRWordBool.RawInit.rowBits false)
      ∃ trace,RunsFrom program
        ⟨0,Tape.mk₂ (rowWord.reverse++List.replicate gap false++true::left) suffix⟩ trace
        ⟨halt,Tape.mk₂ left (true::(List.replicate gap false++rowWord++suffix))⟩ ∧
        trace.length ≤ timeCoefficient*(rowWord.length+gap+1) ∧ ∀ clock,
        visitedSpace program inputLength (trace.take clock) ≤ inputLength+spaceCoefficient*(rowWord.length+gap+1)+1 := by
  refine ⟨34,3,6,machine,34,by decide,by decide,?_⟩
  intro bits gap left suffix inputLength
  simpa only [state,initialTape,finalTape,rows] using return_contract bits gap left suffix inputLength

end PaperProofs.Common.Native.PA17RawInitRowReturn
