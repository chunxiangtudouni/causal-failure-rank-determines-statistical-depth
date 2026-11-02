module
public import Structure.PA17_TM_RatArithmetic_RecordNav_032a

/-! Actual read-only previous-record navigation. The old cache end TRUE and
the original input footer FALSE have distinct, proved physical endpoints. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRecordNav032

open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def prevFieldMachine : Machine 7 := PSTRTMSeq005.seqMachine
  PA17TMRatArithmeticParse002.backOneMachine PA17TMRatArithmeticParse002.fieldBackMachine
def prevAnchorMachine : Machine 10 := PSTRTMSeq005.seqMachine
  prevFieldMachine PA17TMRatArithmeticFieldNav012.headerBackMachine

/-- Fixed thirteen labels. Every backwards move is an actual machine step;
the old TRUE endpoint is detected by reading it after crossing the gap. -/
def recordPrevMachine : Machine 12 := PSTRTMSeq005.seqMachine
  prevAnchorMachine (PA17TMRatArithmeticAllocate013.gapSeekMachine .left)

theorem recordPrev_bounded (gap : Nat) (archive digits suffix : List Bool) :
    BoundedRun recordPrevMachine (nextOutput gap archive true digits suffix) 12
      (nextInput gap archive true digits suffix) (gap+2*digits.length+12) := by
  have hb : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
      (nextOutput gap archive true digits suffix) 1
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap true archive))
        (false::true::suffix)) 2 := by
    exact ⟨PA17TMRatArithmeticParse002.backOneTrace
        (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap true archive))
        false (true::suffix),
      PA17TMRatArithmeticParse002.backOne_runsFrom
        (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap true archive))
        false (true::suffix),by rfl⟩
  have hf : BoundedRun PA17TMRatArithmeticParse002.fieldBackMachine
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap true archive))
        (false::true::suffix)) 5
      (Tape.mk₂ (false::true::oldContext gap true archive) (recordWord digits suffix))
      (2*digits.length+5) := by
    refine ⟨PA17TMRatArithmeticParse002.fieldBackTrace (true::oldContext gap true archive)
        digits (false::true::suffix),
      PA17TMRatArithmeticParse002.fieldBack_runsFrom (true::oldContext gap true archive)
        digits (false::true::suffix),?_⟩
    rw [PA17TMRatArithmeticParse002.fieldBackTrace_length]
  have hh : BoundedRun PA17TMRatArithmeticFieldNav012.headerBackMachine
      (Tape.mk₂ (false::true::oldContext gap true archive) (recordWord digits suffix)) 2
      (Tape.mk₂ (oldContext gap true archive) (true::false::recordWord digits suffix)) 3 := by
    exact ⟨PA17TMRatArithmeticFieldNav012.headerBackTrace (oldContext gap true archive)
        false true (recordWord digits suffix),
      PA17TMRatArithmeticFieldNav012.headerBack_runsFrom (oldContext gap true archive)
        false true (recordWord digits suffix),by rfl⟩
  have hg : BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .left)
      (Tape.mk₂ (oldContext gap true archive) (true::false::recordWord digits suffix)) 1
      (nextInput gap archive true digits suffix) (gap+2) := by
    refine ⟨PA17TMRatArithmeticAllocate013.returnGapTrace gap archive (false::recordWord digits suffix),
      PA17TMRatArithmeticAllocate013.returnGap_runsFrom gap archive (false::recordWord digits suffix),?_⟩
    rw [PA17TMRatArithmeticAllocate013.returnGap_length]
  have h := ((hb.seq hf).seq hh).seq hg
  apply h.mono
  omega

theorem recordPrev_contract (gap : Nat) (archive digits suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom recordPrevMachine
        ⟨0,nextOutput gap archive true digits suffix⟩ trace ⟨12,nextInput gap archive true digits suffix⟩ ∧
      trace.length≤gap+2*digits.length+12 ∧
      ∀ prefixLength chargedL, visitedSpace recordPrevMachine chargedL (trace.take prefixLength) ≤
        chargedL+2*gap+4*digits.length+25 := by
  obtain ⟨trace,hr,hl⟩ := recordPrev_bounded gap archive digits suffix
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le recordPrevMachine chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

private theorem zeros_tail (gap : Nat) (tail : List Bool) :
    List.replicate (gap+2) false++tail=List.replicate gap false++false::false::tail := by
  calc
    _ = (List.replicate gap false++List.replicate 2 false)++tail :=
      congrArg (fun bits : List Bool => bits++tail) (List.replicate_add gap 2 false)
    _ = List.replicate gap false++(List.replicate 2 false++tail) := List.append_assoc _ _ _
    _ = _ := rfl

private theorem zeros_head (gap : Nat) (tail : List Bool) :
    List.replicate (gap+2) false++tail=false::false::(List.replicate gap false++tail) := by
  rw [show gap+2=2+gap by omega,List.replicate_add]
  rfl

/-- The original bank really ends DATA, TRUE FLAG, FALSE END, FALSE footer.
Scanning left stops on the FLAG; two real RIGHTs return to the footer. -/
def originalFooterMachine : Machine 15 :=
  PSTRTMSeq005.seqMachine recordPrevMachine PA17TMRatArithmeticWidth018.headerRightMachine

def originalArchive (archive : List Bool) (lastData : Bool) : List Bool :=
  false::true::lastData::archive

theorem originalFooter_bounded (gap : Nat) (archive : List Bool) (lastData : Bool) (digits suffix : List Bool) :
    BoundedRun originalFooterMachine
      (nextOutput gap (originalArchive archive lastData) false digits suffix) 15
      (nextInput gap (originalArchive archive lastData) false digits suffix) (gap+2*digits.length+17) := by
  have hp := recordPrev_bounded (gap+2) (lastData::archive) digits suffix
  have hp' : BoundedRun recordPrevMachine
      (nextOutput gap (originalArchive archive lastData) false digits suffix) 12
      (Tape.mk₂ (lastData::archive)
        (true::false::false::(List.replicate gap false++true::false::recordWord digits suffix)))
      ((gap+2)+2*digits.length+12) := by
    simp only [nextOutput,recordLeft,oldContext,nextInput] at hp
    rw [zeros_tail gap (true::lastData::archive)] at hp
    rw [zeros_head gap (true::false::recordWord digits suffix)] at hp
    exact hp
  have hh : BoundedRun PA17TMRatArithmeticWidth018.headerRightMachine
      (Tape.mk₂ (lastData::archive)
        (true::false::false::(List.replicate gap false++true::false::recordWord digits suffix))) 2
      (nextInput gap (originalArchive archive lastData) false digits suffix) 3 := by
    exact ⟨PA17TMRatArithmeticWidth018.headerRightTrace (lastData::archive) true false
        (false::(List.replicate gap false++true::false::recordWord digits suffix)),
      PA17TMRatArithmeticWidth018.headerRight_runsFrom (lastData::archive) true false
        (false::(List.replicate gap false++true::false::recordWord digits suffix)),by rfl⟩
  have h := hp'.seq hh
  apply h.mono
  omega

theorem originalFooter_contract (gap : Nat) (archive : List Bool) (lastData : Bool) (digits suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom originalFooterMachine
        ⟨0,nextOutput gap (originalArchive archive lastData) false digits suffix⟩ trace
        ⟨15,nextInput gap (originalArchive archive lastData) false digits suffix⟩ ∧
      trace.length≤gap+2*digits.length+17 ∧
      ∀ prefixLength chargedL, visitedSpace originalFooterMachine chargedL (trace.take prefixLength) ≤
        chargedL+2*gap+4*digits.length+35 := by
  obtain ⟨trace,hr,hl⟩ := originalFooter_bounded gap archive lastData digits suffix
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le originalFooterMachine chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRecordNav032
