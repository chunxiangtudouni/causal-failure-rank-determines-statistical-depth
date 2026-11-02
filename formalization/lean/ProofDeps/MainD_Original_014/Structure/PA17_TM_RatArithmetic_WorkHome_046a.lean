module
public import Structure.PA17_TM_RatArithmetic_ReturnHome_037b
public import Structure.PA17_TM_RatArithmetic_FarLoad_031c

/-! Return from the actual first DATA of an unfinished A workspace.
There is no cache-end TRUE after this field. At the original FALSE footer,
the real LEFT scan stops on Dy's last TRUE FLAG and two RIGHTs reach footer.
The already loaded A field is never inspected or changed. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWorkHome046

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticFieldNav012
open PA17TMRatArithmeticAllocate013 PA17TMRatArithmeticRecordNav032
open PA17TMRatArithmeticReturnHome037

def originalBoundaryMachine : Machine 4 :=
  PSTRTMSeq005.seqMachine (gapSeekMachine .left) headerRightMachine

theorem original_anchor_bounded (gap : Nat) (archive : List Bool) (lastData : Bool) (word : List Bool) :
    BoundedRun originalBoundaryMachine
      (Tape.mk₂ (List.replicate gap false++false::originalArchive archive lastData) (true::false::word)) 4
      (Tape.mk₂ (originalArchive archive lastData)
        (false::(List.replicate gap false++true::false::word))) (gap+7) := by
  have zeros_left : List.replicate gap false++false::false::true::lastData::archive=
      List.replicate (gap+2) false++true::lastData::archive := by
    rw [List.replicate_add]
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc]
  have zeros_front : List.replicate (gap+2) false++true::false::word=
      false::false::(List.replicate gap false++true::false::word) := by
    rw [show gap+2=2+gap by omega,List.replicate_add]
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  have hs : BoundedRun (gapSeekMachine .left)
      (Tape.mk₂ (List.replicate gap false++false::originalArchive archive lastData) (true::false::word)) 1
      (Tape.mk₂ (lastData::archive)
        (true::false::false::(List.replicate gap false++true::false::word))) (gap+4) := by
    refine ⟨returnGapTrace (gap+2) (lastData::archive) (false::word),?_,?_⟩
    · simpa only [originalArchive,zeros_left,zeros_front,seekState] using
        returnGap_runsFrom (gap+2) (lastData::archive) (false::word)
    · rw [returnGap_length]
  have hh : BoundedRun headerRightMachine
      (Tape.mk₂ (lastData::archive)
        (true::false::false::(List.replicate gap false++true::false::word))) 2
      (Tape.mk₂ (originalArchive archive lastData)
        (false::(List.replicate gap false++true::false::word))) 3 :=
    ⟨headerRightTrace (lastData::archive) true false (false::(List.replicate gap false++true::false::word)),
      headerRight_runsFrom (lastData::archive) true false (false::(List.replicate gap false++true::false::word)),by rfl⟩
  have combined := hs.seq hh
  simpa [originalBoundaryMachine,PSTRTMSeq005.rightLabel] using
    combined.mono (by omega : (gap+4)+3≤gap+7)

def originalFooterMachine : Machine 7 := PSTRTMSeq005.seqMachine headerBackMachine originalBoundaryMachine

def originalHomeMachine : Machine 42 := PSTRTMSeq005.seqMachine originalFooterMachine finishBackMachine

theorem original_work_home_bounded (sx : Bool) (counter nx dx ny dyTail : List Bool)
    (gap : Nat) (word : List Bool) :
    BoundedRun originalHomeMachine
      (Tape.mk₂
        (false::true::(List.replicate gap false++false::footerLeft sx counter nx dx ny (false::dyTail))) word) 42
      (Tape.mk₂ counter (prefixRight sx
        (bank nx dx ny (false::dyTail) (List.replicate gap false++true::false::word))))
      (gap+2*bankWidth nx dx ny (false::dyTail)+41) := by
  have hn : (false::dyTail).reverse≠[] := by
    intro hz
    have hl := congrArg List.length hz
    simp at hl
  have ha : BoundedRun originalBoundaryMachine
      (Tape.mk₂ (List.replicate gap false++false::footerLeft sx counter nx dx ny (false::dyTail))
        (true::false::word)) 4
      (Tape.mk₂ (footerLeft sx counter nx dx ny (false::dyTail))
        (false::(List.replicate gap false++true::false::word))) (gap+7) := by
    cases hr : (false::dyTail).reverse with
    | nil => exact (hn hr).elim
    | cons last rest =>
      let archive := PSTRTMRawNat010.leftBlocks rest++false::dyContext sx counter nx dx ny
      have left_eq : footerLeft sx counter nx dx ny (false::dyTail)=originalArchive archive last := by
        simp [footerLeft,hr,PSTRTMRawNat010.leftBlocks,originalArchive,archive]
      have hb := original_anchor_bounded gap archive last word
      rw [←left_eq] at hb
      exact hb
  have hh : BoundedRun headerBackMachine
      (Tape.mk₂
        (false::true::(List.replicate gap false++false::footerLeft sx counter nx dx ny (false::dyTail))) word) 2
      (Tape.mk₂ (List.replicate gap false++false::footerLeft sx counter nx dx ny (false::dyTail))
        (true::false::word)) 3 :=
    ⟨headerBackTrace _ false true word,headerBack_runsFrom _ false true word,by rfl⟩
  have hf := finishBack_bounded sx counter nx dx ny (false::dyTail)
    (List.replicate gap false++true::false::word)
  have combined := (hh.seq ha).seq hf
  have cost : (3+(gap+7))+(2*bankWidth nx dx ny (false::dyTail)+31)≤
      gap+2*bankWidth nx dx ny (false::dyTail)+41 := by omega
  simpa [originalHomeMachine,originalFooterMachine,PSTRTMSeq005.rightLabel] using combined.mono cost

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWorkHome046
