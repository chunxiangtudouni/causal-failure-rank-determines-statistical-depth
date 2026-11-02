module
public import Structure.RootB23_Threshold_ReturnAnchor_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnQuarter
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

/-- The TRUE cap-B has EOF01 before its actual bare quarter, not OWN00.
This fixed scanner consumes four literal quarter prefix pairs until the
first genuine false flag, then makes eight real LEFTs to the quarter tag.
The next original-B far-copy route uses this exact physical connector. -/
def fourLeft (tape : Tape Bool) : Tape Bool := (((tape.move .left).move .left).move .left).move .left
def eightCode : Machine 9 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdRewind124.fourMachine PSTRTMThresholdRewind124.fourMachine
def code : Machine 11 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine eightCode

theorem eight_bounded (tape : Tape Bool) :
    BoundedRun eightCode tape 9 (fourLeft (fourLeft tape)) 10 := by
  have first : BoundedRun PSTRTMThresholdRewind124.fourMachine tape 4 (fourLeft tape) 5 :=
    ⟨PSTRTMThresholdRewind124.fourTrace tape,PSTRTMThresholdRewind124.four_runsFrom tape,by rfl⟩
  have second : BoundedRun PSTRTMThresholdRewind124.fourMachine (fourLeft tape) 4
      (fourLeft (fourLeft tape)) 5 :=
    ⟨PSTRTMThresholdRewind124.fourTrace (fourLeft tape),
      PSTRTMThresholdRewind124.four_runsFrom (fourLeft tape),by rfl⟩
  exact first.seq second

theorem actual_bounded (left digits suffix : List Bool) :
    BoundedRun code
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++false::(PSTRTMThresholdCapLiteral242.quarterBits++suffix))) 11
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left))
        (PSTRTMThresholdCapLiteral242.quarterBits++suffix)) (2*digits.length+20) := by
  let extended:=digits++[false,false,false,true]
  let atDelimiter:=Tape.mk₂ (true::(PSTRTMRawNat010.leftBlocks extended.reverse++left))
    (false::false::false::true::suffix)
  have word : PSTRTMIncrement009.blocks digits++false::(PSTRTMThresholdCapLiteral242.quarterBits++suffix)=
      PSTRTMIncrement009.blocks extended++true::false::false::false::true::suffix := by
    simp [extended,PSTRTMIncrement009.blocks,List.flatMap_append,PSTRTMThresholdCapLiteral242.quarterBits]
  have scanned : BoundedRun PA17TMRatArithmeticWidth018.scanMachine
      (Tape.mk₂ left (PSTRTMIncrement009.blocks extended++true::false::false::false::true::suffix)) 1
      atDelimiter (2*extended.length+2) :=
    ⟨PA17TMRatArithmeticWidth018.scanTrace left extended true (false::false::true::suffix),
      PA17TMRatArithmeticWidth018.scan_runsFrom _ _ _ _,
      by rw [PA17TMRatArithmeticWidth018.scanTrace_length]⟩
  rw [←word] at scanned
  have back:=eight_bounded atDelimiter
  have finalEq : fourLeft (fourLeft atDelimiter)=
      Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left))
        (PSTRTMThresholdCapLiteral242.quarterBits++suffix) := by
    simp [atDelimiter,extended,fourLeft,List.reverse_append,PSTRTMRawNat010.leftBlocks,
      Tape.mk₂,PSTRTMThresholdCapLiteral242.quarterBits]
  rw [finalEq] at back
  have actual:=scanned.seq back
  have port : PSTRTMSeq005.rightLabel (a:=1) (9 : Fin 10)=(11 : Fin 12) := by decide
  rw [port] at actual
  exact actual.mono (by simp only [extended,List.length_append,List.length_cons,List.length_nil];omega)

end RootB23.Threshold.ReturnQuarter
