module
public import Structure.B23_5_RawInit_FinalSwitch031

/-! Fixed original-input assembler awaiting the one producer+Fin16 callee.
The internal premise is a genuine RunsFrom on the exact archive produced
by PaddedFront, not a supplied answer or a host-selected transition table.
An actual physical second-cell branch shares ONE positive callee. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.CompleteWiring
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicCursorArchive
open RationalControllerComputation.PSTRSymbolicLaneArchive
open RationalControllerComputation.PSTRSymbolicLaneScan
open RationalControllerComputation.PSTRTMRawNat010
open RationalControllerComputation.PSTRTMIncrement009
variable {a : Nat}

theorem follow_actual (positive : Machine a) (positiveClock : Nat → Nat)
    (positiveActual : ∀ data : List Datum, data≠[] → ∀ digits : List Bool,
      2≤digits.length → digits.length≤(PSTRTMNatValue017.rawPayload data.length).length+1 →
      valueDigits digits≤1 → ∃ path final,
        RunsFrom positive ⟨0,archiveTape data
          (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) digits [] true⟩ path final ∧
        final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
        path.length≤positiveClock (encode data).length)
    (data : List Datum) (tape : Tape Bool) (output : PaddedFront.outcome data tape) :
    ∃ path final, RunsFrom (FinalSwitch.machine positive) ⟨0,tape⟩ path final ∧
      final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
      path.length≤positiveClock (encode data).length+3 := by
  by_cases empty : data=[]
  · subst data
    obtain ⟨path,run,time⟩:=FinalSwitch.empty_fin16 positive
    refine ⟨path,⟨2,Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode []))⟩,?_,rfl,?_⟩
    · rw [show tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode [])) from output]
      exact run
    · omega
  · obtain ⟨digits,tapeEq,lower,upper,value⟩:=PaddedArchive.shape data empty tape output
    obtain ⟨back,backFinal,backRun,backTape,backTime⟩:=positiveActual data empty digits lower upper value
    let left:=(navigationCells (allDatumPairs data)).reverse++false::
      (leftBlocks digits.reverse++false::false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length))
    have backFrom : RunsFrom positive ⟨0,Tape.mk₂ left [true]⟩ back backFinal := by
      simpa only [archiveTape,left] using backRun
    obtain ⟨path,run,time⟩:=FinalSwitch.positive_actual positive left back backFinal backFrom
    refine ⟨path,FinalSwitch.bodyCfg backFinal,?_,backTape,?_⟩
    · have inputEq : tape=Tape.mk₂ left [true] := by simpa only [archiveTape,left] using tapeEq
      rw [inputEq]
      exact run
    · omega

noncomputable abbrev frontStates : Nat := (Dispatch.support PaddedFront.sizes).card+0+1
noncomputable abbrev bridgeStates (a : Nat) : Nat := frontStates+(a+3)+1
noncomputable def bridge (positive : Machine a) : Machine (bridgeStates a) :=
  seqMachine (a:=frontStates) (b:=a+3) PaddedFront.machine (FinalSwitch.machine positive)
noncomputable def machine (positive : Machine a) : Machine (bridgeStates a+0+1) :=
  seqMachine (a:=bridgeStates a) (b:=0) (bridge positive) PaddedFront.sink
noncomputable def haltPort (a : Nat) : Fin ((bridgeStates a+0+1)+1) :=
  rightLabel (a:=bridgeStates a) (b:=0) 0

theorem finish_tape {states : Nat} (cfg : MachineState states) (target : Tape Bool)
    (same : cfg.Tape=target) :
    (rightCfg (a:=states) (b:=0) (⟨0,cfg.Tape⟩ : MachineState 0)).Tape=target := same

theorem actual (positive : Machine a) (positiveClock : Nat → Nat)
    (positiveActual : ∀ data : List Datum, data≠[] → ∀ digits : List Bool,
      2≤digits.length → digits.length≤(PSTRTMNatValue017.rawPayload data.length).length+1 →
      valueDigits digits≤1 → ∃ path final,
        RunsFrom positive ⟨0,archiveTape data
          (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) digits [] true⟩ path final ∧
        final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
        path.length≤positiveClock (encode data).length)
    (data : List Datum) : ∃ path final,
    Runs (machine positive) (encode data) path final ∧ final.q=haltPort a ∧
      final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
      path.length≤32000*((encode data).length+1)^3+positiveClock (encode data).length+4 ∧
      ∀ inputLen clock, visitedSpace (machine positive) inputLen (path.take clock)≤
        inputLen+2*(32000*((encode data).length+1)^3+positiveClock (encode data).length+4)+1 := by
  obtain ⟨front,frontFinal,frontRun,_frontPort,frontTape,frontTime,_frontSpace⟩:=PaddedFront.actual data
  obtain ⟨back,backFinal,backRun,backTape,backTime⟩:=
    follow_actual positive positiveClock positiveActual data frontFinal.Tape frontTape
  let middlePath:=front.map (leftCfg (b:=a+3))++back.map (rightCfg (a:=frontStates))
  let middleFinal:=rightCfg (a:=frontStates) backFinal
  have middleRun : Runs (bridge positive) (encode data) middlePath middleFinal :=
    seq_runs (a:=frontStates) (b:=a+3) PaddedFront.machine (FinalSwitch.machine positive)
      (encode data) frontFinal backFinal front back frontRun backRun
  let path:=middlePath.map (leftCfg (b:=0))++
    [rightCfg (a:=bridgeStates a) (b:=0) ⟨0,middleFinal.Tape⟩]
  let final:=rightCfg (a:=bridgeStates a) (b:=0) ⟨0,middleFinal.Tape⟩
  have time : path.length≤32000*((encode data).length+1)^3+positiveClock (encode data).length+4 := by
    simp only [path,middlePath,List.length_append,List.length_map,List.length_cons,List.length_nil]
    omega
  refine ⟨path,final,PaddedFront.finish (bridge positive) (encode data) middlePath middleFinal middleRun,
    rfl,?_,time,?_⟩
  · exact finish_tape middleFinal _ (LargeArchive.transport_tape backFinal _ backTape)
  · intro inputLen clock
    have cells:=PSTRTMTrace002.visitedSpace_le (machine positive) inputLen (path.take clock)
    have short:=(List.length_take_le' clock path).trans time
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.CompleteWiring
