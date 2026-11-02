module
public import Common.PSTR_TM_B1RunFrame_122

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1ResidentFrame123
open PaperProofs.Common.Native.RationalControllerComputation

def sourcePairs (numerator denominator : Nat) : List (Bool × Bool) :=
  PSTRTMPackCode036.digitPairs (PSTRTMNatValue017.rawPayload numerator) (PSTRTMNatValue017.rawPayload denominator)

/-- SAME fixed32-label allocation and82-label finite B1 loop. The archive
is real retained tape behind a real false guard, not an oracle argument
to the fixed code. All work/counter allocation occurs on actual blanks. -/
def residentMachine : Machine 113 := PSTRTMSeq005.seqMachine
  PSTRTMB1PrepareCode069.prepareMachine PSTRTMB1LoopCode071.loopMachine

def residentTrace (archive : List Bool) (numerator denominator : Nat) : List (MachineState 113) :=
  (PSTRTMB1PrepareFrame119.prepareTrace archive (sourcePairs numerator denominator)).map (PSTRTMSeq005.leftCfg (b:=81)) ++
    (PSTRTMB1RunFrame122.loopTrace archive numerator denominator).map (PSTRTMSeq005.rightCfg (a:=31))

def residentInitial (archive : List Bool) (numerator denominator : Nat) : MachineState 113 :=
  PSTRTMSeq005.leftCfg (b:=81) (PSTRTMB1PrepareCode069.state 0 (false::archive)
    (PSTRTMBinaryAdd024.operandColumns (sourcePairs numerator denominator)))

def residentFinal (archive : List Bool) (numerator denominator : Nat) : MachineState 113 :=
  PSTRTMSeq005.rightCfg (a:=31) (PSTRTMB1RunFrame122.loopFinal archive numerator denominator)

theorem resident_runsFrom (archive : List Bool) (numerator denominator : Nat) (hn : 0 < numerator) :
    PSTRTMSeq005.RunsFrom residentMachine (residentInitial archive numerator denominator)
      (residentTrace archive numerator denominator) (residentFinal archive numerator denominator) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMB1PrepareCode069.prepareMachine PSTRTMB1LoopCode071.loopMachine
    (PSTRTMB1PrepareCode069.state 0 (false::archive) (PSTRTMBinaryAdd024.operandColumns (sourcePairs numerator denominator)))
    (PSTRTMB1PrepareFrame119.prepareFinal archive (sourcePairs numerator denominator))
    (PSTRTMB1RunFrame122.loopFinal archive numerator denominator)
    (PSTRTMB1PrepareFrame119.prepareTrace archive (sourcePairs numerator denominator))
    (PSTRTMB1RunFrame122.loopTrace archive numerator denominator)
    (PSTRTMB1PrepareFrame119.prepare_runsFrom archive (sourcePairs numerator denominator))
  exact PSTRTMB1RunFrame122.loop_runsFrom archive numerator denominator hn

/-- ENTIRE final tape, including the retained archive, actual cleared
source/marker cells and actual canonical binary counter head position. -/
theorem resident_final_tape (archive : List Bool) (numerator denominator : Nat) :
    (residentFinal archive numerator denominator).Tape = Turing.Tape.mk₂
      (List.replicate (4*PSTRTMB1RunFrame122.width numerator denominator+5) false ++ archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PSTRTMB1Value068.exponent numerator denominator))) :=
  PSTRTMB1RunFrame122.loop_final_tape archive numerator denominator

theorem source_length (numerator denominator : Nat) :
    (sourcePairs numerator denominator).length ≤ natBits numerator+natBits denominator := by
  simp only [sourcePairs,PSTRTMPackCode036.digitPairs_length,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  omega

private theorem arithmetic_length_bound (first second n m : Nat)
    (hf : first≤8*(n+m)+33) (hs : second≤128*(n+m+1)^2) :
    first+second ≤ 256*(n+m+1)^2 := by nlinarith

theorem resident_length_le (archive : List Bool) (numerator denominator : Nat) (hn : 0 < numerator) :
    (residentTrace archive numerator denominator).length ≤ 256*(natBits numerator+natBits denominator+1)^2 := by
  have hp := PSTRTMB1PrepareFrame119.prepare_length archive (sourcePairs numerator denominator)
  have hw := source_length numerator denominator
  have hl := PSTRTMB1RunFrame122.loop_length_le archive numerator denominator hn
  have hp' : (PSTRTMB1PrepareFrame119.prepareTrace archive (sourcePairs numerator denominator)).length ≤
      8*(natBits numerator+natBits denominator)+33 := by omega
  simp only [residentTrace,List.length_append,List.length_map]
  exact arithmetic_length_bound _ _ _ _ hp' hl

private theorem arithmetic_space_bound (archive n m pairs time space : Nat)
    (hp : pairs≤n+m) (ht : time≤256*(n+m+1)^2)
    (hs : space≤archive+1+4*pairs+2*time+1) : space≤archive+1024*(n+m+1)^2 := by nlinarith

/-- ORIGINAL visitedSpace of the SAME actual trace. The initial charged
length includes the real archived cells; archive data are not cost fields. -/
theorem resident_visitedSpace_le (archive : List Bool) (numerator denominator : Nat) (hn : 0 < numerator) :
    visitedSpace residentMachine (archive.length+1+4*(sourcePairs numerator denominator).length)
      (residentTrace archive numerator denominator) ≤ archive.length+1024*(natBits numerator+natBits denominator+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le residentMachine
    (archive.length+1+4*(sourcePairs numerator denominator).length) (residentTrace archive numerator denominator)
  exact arithmetic_space_bound _ _ _ _ _ _ (source_length numerator denominator)
    (resident_length_le archive numerator denominator hn) hs

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1ResidentFrame123
