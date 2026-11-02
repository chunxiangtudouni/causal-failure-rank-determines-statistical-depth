module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023k
public import Structure.PA17_TM_RatArithmetic_BankWalk_033b

/-! Seed the far TRUE once, while the latest cache end has genuinely blank
right tail. Reuse the frozen real marker program, including its temporary
FALSE and its paid restoration; this is never a repeated-per-flag step. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036

open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033 (RecordSpec bankTail bankLeft bankStart bankEnd totalGap totalWidth)

def gapWord (n : Nat) : List Bool := PA17TMRatArithmeticAllocatePass023.gapTail n

def bankTape (archive : List Bool) (records : List RecordSpec) (n : Nat) : Tape Bool :=
  Tape.mk₂ archive (false::bankTail records (gapWord n))

def farSeedMachine : Machine 6 :=
  PSTRTMSeq005.seqMachine PA17TMRatArithmeticBookmark014.markerMachine
    (PA17TMRatArithmeticAllocate013.setMarkerMachine true)

theorem far_seed_bounded (archive : List Bool) :
    BoundedRun (s:=6) farSeedMachine (Tape.mk₂ archive [true]) 6
      (Tape.mk₂ archive [true,true]) 7 := by
  have hm : BoundedRun (s:=4) PA17TMRatArithmeticBookmark014.markerMachine
      (Tape.mk₂ archive [true]) 4 (Tape.mk₂ archive [false,true]) 5 :=
    ⟨PA17TMRatArithmeticBookmark014.markerTrace archive,
     PA17TMRatArithmeticBookmark014.marker_runsFrom archive,by rfl⟩
  have ht : BoundedRun (s:=1) (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ archive [false,true]) 1 (Tape.mk₂ archive [true,true]) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false true archive [true],
     PA17TMRatArithmeticAllocate013.setMarker_runsFrom false true archive [true],by rfl⟩
  exact hm.seq ht

theorem far_seed_contract (archive : List Bool) (chargedLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom farSeedMachine ⟨0,Tape.mk₂ archive [true]⟩ trace
      ⟨6,Tape.mk₂ archive [true,true]⟩ ∧ trace.length≤7 ∧
      ∀ prefixLength, visitedSpace farSeedMachine chargedLength (trace.take prefixLength)≤chargedLength+15 := by
  obtain ⟨trace,hr,hl⟩ := far_seed_bounded archive
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength
  have hs := PSTRTMTrace002.visitedSpace_le farSeedMachine chargedLength (trace.take prefixLength)
  have hp : (trace.take prefixLength).length≤trace.length := by simp only [List.length_take];omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
