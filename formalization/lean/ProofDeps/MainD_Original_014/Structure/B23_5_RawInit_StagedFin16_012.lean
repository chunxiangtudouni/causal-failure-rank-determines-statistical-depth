module
public import Structure.B23_5_RawInit_ReverseCleanup011

/-! Full physical staged-bit export and cleanup into the exact Fin16 Tape.
The pending original RawInit producer must establish stagedTape from raw
encode data. No such producer is assumed or claimed here. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.StagedFin16
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

def machine : Machine 432 := seqMachine ReverseLoop.machine ReverseCleanup.machine
def haltPort : Fin 433 := rightLabel (a:=422) (b:=9) 9
def stagedTape (data : List Datum) (gap : Nat) : Tape Bool :=
  ReverseLoop.tape (rawPrefix data).reverse [] gap []

theorem actual (data : List Datum) (gap : Nat) : ∃ path final,
    RunsFrom machine ⟨0,stagedTape data gap⟩ path final ∧ final.q=haltPort ∧
      final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
      path.length≤220*((encode data).length+gap+1)^2 ∧ ∀ clock,
        visitedSpace machine (encode data).length (path.take clock)≤
          1024*((encode data).length+gap+1)^2 := by
  let remaining := (rawPrefix data).reverse
  obtain ⟨front,frontRun,frontTime,_frontSpace⟩ :=
    ReverseLoop.actual_with_resources remaining [] [] gap (encode data).length
  obtain ⟨back,backRun,backTime,_backSpace⟩ :=
    ReverseCleanup.actual (rawPrefix data) remaining gap (encode data).length
  have backRun' : RunsFrom ReverseCleanup.machine
      ⟨0,(ReverseLoop.finish (remaining.reverse++[]) gap ([]++remaining)).Tape⟩ back
      (ReverseCleanup.final remaining) := by
    simpa only [ReverseCleanup.initial,ReverseLoop.finish,remaining,List.reverse_reverse,
      List.append_nil,List.nil_append] using backRun
  let path := front.map (leftCfg (b:=9))++back.map (rightCfg (a:=422))
  let final := rightCfg (a:=422) (ReverseCleanup.final remaining)
  have run := seq_runsFrom ReverseLoop.machine ReverseCleanup.machine
    (ReverseLoop.state remaining [] gap []) _ _ front back frontRun backRun'
  have inputLength : (encode data).length=(rawPrefix data).length+1 := raw_input_length data
  have time : path.length≤220*((encode data).length+gap+1)^2 := by
    simp only [remaining,List.length_reverse,List.length_nil,Nat.add_zero] at frontTime backTime
    simp only [path,List.length_append,List.length_map]
    rw [inputLength]
    nlinarith [Nat.zero_le ((rawPrefix data).length^2),Nat.zero_le (gap^2)]
  refine ⟨path,final,?_,rfl,?_,time,?_⟩
  · simpa [machine,ReverseLoop.state,stagedTape,path,leftCfg,leftLabel,remaining,final] using run
  · change Tape.mk₁ (RowEnd.rows remaining)=_
    rw [encoded_raw_shape]
    rfl
  · intro clock
    have cells := PSTRTMTrace002.visitedSpace_le machine (encode data).length (path.take clock)
    have take := (List.length_take_le' clock path).trans time
    have inputBound : (encode data).length≤((encode data).length+gap+1)^2 := by nlinarith
    have positive : 0<((encode data).length+gap+1)^2 := by positivity
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.StagedFin16
