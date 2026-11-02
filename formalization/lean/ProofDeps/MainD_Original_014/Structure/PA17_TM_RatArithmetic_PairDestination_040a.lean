module
public import Structure.PA17_TM_RatArithmetic_RecordNav_032a
public import Structure.PA17_TM_RatArithmetic_Width_018f
public import Structure.PA17_TM_RatArithmetic_FieldNav_012a

/-! Actual destination transport when operand B shares operand A's OWN
cell. A is a flagged field of arbitrary digits; its first bit need not be
FALSE. The shared B first DATA must remain physically FALSE until copying
has finished. Every scan and return is actual code, with no width in code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairDestination040

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticAllocate013 PA17TMRatArithmeticFieldNav012

def toADataMachine : Machine 4 :=
  PSTRTMSeq005.seqMachine (gapSeekMachine .right) headerRightMachine

def outToBMachine : Machine 6 := PSTRTMSeq005.seqMachine toADataMachine scanMachine

theorem out_to_B_bounded (oldBit : Bool) (archive digits bTail : List Bool) (gap : Nat) :
    BoundedRun outToBMachine
      (Tape.mk₂ archive (oldBit::(List.replicate gap false++true::false::
        (PSTRTMIncrement009.blocks digits++false::false::bTail)))) 6
      (Tape.mk₂
        (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::
          (List.replicate gap false++oldBit::archive)))
        (false::bTail))
      (gap+2*digits.length+7) := by
  let firstField := PSTRTMIncrement009.blocks digits++false::false::bTail
  let oldLeft := List.replicate gap false++oldBit::archive
  have hg : BoundedRun (gapSeekMachine .right)
      (Tape.mk₂ archive (oldBit::(List.replicate gap false++true::false::firstField))) 1
      (Tape.mk₂ oldLeft (true::false::firstField)) (gap+2) := by
    refine ⟨PA17TMRatArithmeticRecordNav032.gapRightTrace gap archive oldBit (false::firstField),?_,?_⟩
    · exact PA17TMRatArithmeticRecordNav032.gapRight_runsFrom gap archive oldBit (false::firstField)
    · rw [PA17TMRatArithmeticRecordNav032.gapRightTrace_length]
  have hh : BoundedRun headerRightMachine
      (Tape.mk₂ oldLeft (true::false::firstField)) 2
      (Tape.mk₂ (false::true::oldLeft) firstField) 3 :=
    ⟨headerRightTrace oldLeft true false firstField,
      headerRight_runsFrom oldLeft true false firstField,by rfl⟩
  have hs : BoundedRun scanMachine (Tape.mk₂ (false::true::oldLeft) firstField) 1
      (Tape.mk₂
        (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldLeft))
        (false::bTail)) (2*digits.length+2) :=
    ⟨scanTrace (false::true::oldLeft) digits false bTail,
      scan_runsFrom (false::true::oldLeft) digits false bTail,by rw [scanTrace_length]⟩
  have combined := (hg.seq hh).seq hs
  have cost : ((gap+2)+3)+(2*digits.length+2)≤gap+2*digits.length+7 := by omega
  simpa [outToBMachine,toADataMachine,PSTRTMSeq005.rightLabel,firstField,oldLeft] using
    combined.mono cost

def fromBGuardMachine : Machine 7 := PSTRTMSeq005.seqMachine footerMachine fieldBackMachine

def toAAnchorMachine : Machine 10 := PSTRTMSeq005.seqMachine fromBGuardMachine headerBackMachine

def backFromBMachine : Machine 12 :=
  PSTRTMSeq005.seqMachine toAAnchorMachine (gapSeekMachine .left)

theorem back_from_B_bounded (archive digits bTail : List Bool) (gap : Nat) :
    BoundedRun backFromBMachine
      (Tape.mk₂
        (PSTRTMRawNat010.leftBlocks digits.reverse++false::true::
          (List.replicate gap false++true::archive))
        (false::false::bTail)) 12
      (Tape.mk₂ archive (true::(List.replicate gap false++true::false::
        (PSTRTMIncrement009.blocks digits++false::false::bTail))))
      (gap+2*digits.length+12) := by
  let oldLeft := List.replicate gap false++true::archive
  let aLeft := PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldLeft
  let firstField := PSTRTMIncrement009.blocks digits++false::false::bTail
  have hr : BoundedRun footerMachine (Tape.mk₂ aLeft (false::false::bTail)) 1
      (Tape.mk₂ (false::aLeft) (false::bTail)) 2 := by
    refine ⟨[cursorState 0 aLeft (false::false::bTail),
      cursorState 1 (false::aLeft) (false::bTail)],?_,by rfl⟩
    refine ⟨rfl,?_,rfl,?_⟩
    · simp [List.isChain_cons_cons,TM0.step,footerMachine,cursorState,Tape.mk₂]
    · simp [TM0.step,footerMachine]
  have hb : BoundedRun fieldBackMachine (Tape.mk₂ (false::aLeft) (false::bTail)) 5
      (Tape.mk₂ (false::true::oldLeft) firstField) (2*digits.length+5) :=
    ⟨fieldBackTrace (true::oldLeft) digits (false::bTail),
      fieldBack_runsFrom (true::oldLeft) digits (false::bTail),by rw [fieldBackTrace_length]⟩
  have hh : BoundedRun headerBackMachine (Tape.mk₂ (false::true::oldLeft) firstField) 2
      (Tape.mk₂ oldLeft (true::false::firstField)) 3 :=
    ⟨headerBackTrace oldLeft false true firstField,
      headerBack_runsFrom oldLeft false true firstField,by rfl⟩
  have hg : BoundedRun (gapSeekMachine .left) (Tape.mk₂ oldLeft (true::false::firstField)) 1
      (Tape.mk₂ archive (true::(List.replicate gap false++true::false::firstField))) (gap+2) :=
    ⟨returnGapTrace gap archive (false::firstField),
      returnGap_runsFrom gap archive (false::firstField),by rw [returnGap_length]⟩
  have combined := ((hr.seq hb).seq hh).seq hg
  have cost : ((2+(2*digits.length+5))+3)+(gap+2)≤gap+2*digits.length+12 := by omega
  simpa [backFromBMachine,toAAnchorMachine,fromBGuardMachine,PSTRTMSeq005.rightLabel,
    firstField,oldLeft,aLeft] using combined.mono cost

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairDestination040
