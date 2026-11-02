module
public import RootB235_ArchiveStaging_Public012
public import Structure.B23_5_RawInit_CompleteWiring032

/-! Complete original-input RawInit. The Root-frozen physical producer,
Staged012 and the proved real all-branch front are installed once before
every data list. All internal work-width facts come from PaddedArchive;
there are no premises on the original input and no staging oracle. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Actual
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicCursorArchive
open RationalControllerComputation.PSTRTMIncrement009

noncomputable abbrev producerStates : Nat := ArchiveStaging.Control.support.card
noncomputable abbrev positiveStates : Nat := producerStates+432+1
noncomputable def positive : Machine positiveStates :=
  seqMachine (a:=producerStates) (b:=432) ArchiveStaging.Public.machine StagedFin16.machine
def positiveClock (size : Nat) : Nat := 10000000*(size+1)^3+220*(size+1)^2

theorem seq_zero {a b : Nat} (first : Machine a) (second : Machine b) (tape : Tape Bool)
    (front : List (MachineState a)) (mid : MachineState a)
    (back : List (MachineState b)) (final : MachineState b)
    (frontRun : RunsFrom first ⟨0,tape⟩ front mid)
    (backRun : RunsFrom second ⟨0,mid.Tape⟩ back final) :
    RunsFrom (seqMachine first second) ⟨0,tape⟩
      (front.map (leftCfg (b:=b))++back.map (rightCfg (a:=a))) (rightCfg (a:=a) final) :=
  seq_runsFrom first second ⟨0,tape⟩ mid final front back frontRun backRun

theorem positive_actual (data : List Datum) (work : List Bool)
    (width : 2≤work.length)
    (workRoom : work.length≤(PSTRTMNatValue017.rawPayload data.length).length+1) :
    ∃ path final, RunsFrom positive
      ⟨0,archiveTape data (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) work [] true⟩ path final ∧
      final.q=rightLabel (a:=producerStates) (b:=432) StagedFin16.haltPort ∧
      final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
      path.length≤positiveClock (encode data).length := by
  obtain ⟨front,mid,frontRun,_frontPort,frontTape,frontTime,_frontSpace⟩:=
    ArchiveStaging.Public.actual data work width workRoom
  obtain ⟨back,backFinal,backRun,backPort,backTape,backTime,_backSpace⟩:=StagedFin16.actual data 0
  have backFrom : RunsFrom StagedFin16.machine ⟨0,mid.Tape⟩ back backFinal := by
    rw [frontTape]
    exact backRun
  let path:=front.map (leftCfg (b:=432))++back.map (rightCfg (a:=producerStates))
  let final:=rightCfg (a:=producerStates) backFinal
  have run : RunsFrom positive
      ⟨0,archiveTape data (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) work [] true⟩ path final :=
    seq_zero ArchiveStaging.Public.machine StagedFin16.machine _ front mid back backFinal frontRun backFrom
  refine ⟨path,final,run,LargeArchive.transport_port backFinal _ backPort,
    LargeArchive.transport_tape backFinal _ backTape,?_⟩
  simp only [path,List.length_append,List.length_map,positiveClock]
  simpa only [Nat.add_zero] using Nat.add_le_add frontTime backTime

theorem positive_for_wiring : ∀ data : List Datum, data≠[] → ∀ digits : List Bool,
    2≤digits.length → digits.length≤(PSTRTMNatValue017.rawPayload data.length).length+1 →
    valueDigits digits≤1 → ∃ path final,
      RunsFrom positive ⟨0,archiveTape data
        (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) digits [] true⟩ path final ∧
      final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
      path.length≤positiveClock (encode data).length := by
  intro data _ digits lower upper _
  obtain ⟨path,final,run,_port,tape,time⟩:=positive_actual data digits lower upper
  exact ⟨path,final,run,tape,time⟩

noncomputable abbrev states : Nat := CompleteWiring.bridgeStates positiveStates+0+1
noncomputable def machine : Machine states := CompleteWiring.machine positive
noncomputable def haltPort : Fin (states+1) := CompleteWiring.haltPort positiveStates

theorem clock_room (size : Nat) :
    32000*(size+1)^3+positiveClock size+4≤10033000*(size+1)^3 := by
  have square:=PaddedFront.square_le_cube size
  have positive : 0<(size+1)^3 := by positivity
  simp only [positiveClock]
  omega

theorem space_room (size : Nat) :
    size+2*(10033000*(size+1)^3)+1≤30000000*(size+1)^3 := by
  nlinarith only [Nat.zero_le (size^2),Nat.zero_le (size^3)]

theorem actual (data : List Datum) : ∃ path final,
    Runs machine (encode data) path final ∧ final.q=haltPort ∧ TM0.step machine final=none ∧
      final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
      path.length≤10033000*((encode data).length+1)^3 ∧ ∀ clock,
        visitedSpace machine (encode data).length (path.take clock)≤
          30000000*((encode data).length+1)^3 := by
  obtain ⟨path,final,run,port,tape,time,_space⟩:=
    CompleteWiring.actual positive positiveClock positive_for_wiring data
  have bound : path.length≤10033000*((encode data).length+1)^3 :=
    time.trans (clock_room (encode data).length)
  refine ⟨path,final,run,port,run.2.2.2.1,tape,bound,?_⟩
  intro clock
  have cells:=PSTRTMTrace002.visitedSpace_le machine (encode data).length (path.take clock)
  have short:=(List.length_take_le' clock path).trans bound
  exact (cells.trans (by omega)).trans (space_room (encode data).length)

theorem fixed_adapter : ∃ (stateCount : Nat) (program : Machine stateCount)
    (halt : Fin (stateCount+1)) (c d : Nat), 0<c ∧ 0<d ∧
    ∀ data : List Datum, ∃ path final, Runs program (encode data) path final ∧
      final.q=halt ∧ TM0.step program final=none ∧
      final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
      path.length≤c*((encode data).length+1)^d ∧ ∀ clock,
        visitedSpace program (encode data).length (path.take clock)≤c*((encode data).length+1)^d := by
  refine ⟨states,machine,haltPort,30000000,3,by decide,by decide,?_⟩
  intro data
  obtain ⟨path,final,run,port,stopped,tape,time,space⟩:=actual data
  exact ⟨path,final,run,port,stopped,tape,
    time.trans (Nat.mul_le_mul_right _ (by decide : 10033000≤30000000)),space⟩

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Actual
