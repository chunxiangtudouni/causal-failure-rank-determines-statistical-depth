module
public import Structure.PA17_TM_RatArithmetic_ClearInput_035c
public import Structure.PA17_TM_RatArithmetic_EraseBank_034a

/-! Real final return over ALREADY ERASED cells. Seek the retained original
header TRUE, physically clear it, then seek the already-produced output's
first TRUE. All separating zeros are an actual Tape contract, not an EOF or
answer oracle. The program has no length/width argument. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticClearInput035

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticAllocate013

def clearMarkerMachine : Machine 3 :=
  PSTRTMSeq005.seqMachine (gapSeekMachine .left) (setMarkerMachine false)

def returnOutputMachine : Machine 5 :=
  PSTRTMSeq005.seqMachine clearMarkerMachine (gapSeekMachine .right)

theorem return_output_bounded (leftZeros gap : Nat) (archive word : List Bool) :
    BoundedRun returnOutputMachine
      (Tape.mk₂ (List.replicate leftZeros false++true::archive)
        (false::(List.replicate gap false++true::word))) 5
      (Tape.mk₂ (List.replicate (leftZeros+gap+2) false++archive) (true::word))
      (2*leftZeros+gap+7) := by
  let suffix := List.replicate gap false++true::word
  let middle := List.replicate leftZeros false++false::suffix
  let rightZeros := leftZeros+1+gap
  have hl : BoundedRun (gapSeekMachine .left)
      (Tape.mk₂ (List.replicate leftZeros false++true::archive) (false::suffix)) 1
      (Tape.mk₂ archive (true::middle)) (leftZeros+2) := by
    refine ⟨PA17TMRatArithmeticEraseBank034.returnAnyTrace leftZeros archive false suffix,?_,?_⟩
    · simpa only [middle,seekState] using
        PA17TMRatArithmeticEraseBank034.returnAny_runsFrom leftZeros archive false suffix
    · rw [PA17TMRatArithmeticEraseBank034.returnAnyTrace_length]
  have hw : BoundedRun (setMarkerMachine false) (Tape.mk₂ archive (true::middle)) 1
      (Tape.mk₂ archive (false::middle)) 2 :=
    ⟨setMarkerTrace true false archive middle,setMarker_runsFrom true false archive middle,by rfl⟩
  have middle_eq : middle=List.replicate rightZeros false++true::word := by
    change List.replicate leftZeros false++
      (List.replicate 1 false++(List.replicate gap false++true::word)) = _
    rw [zeros_join,zeros_join]
  have hr : BoundedRun (gapSeekMachine .right) (Tape.mk₂ archive (false::middle)) 1
      (Tape.mk₂ (List.replicate rightZeros false++false::archive) (true::word)) (rightZeros+2) := by
    refine ⟨PA17TMRatArithmeticRecordNav032.gapRightTrace rightZeros archive false word,?_,?_⟩
    · simpa only [middle_eq] using
        PA17TMRatArithmeticRecordNav032.gapRight_runsFrom rightZeros archive false word
    · rw [PA17TMRatArithmeticRecordNav032.gapRightTrace_length]
  have combined := (hl.seq hw).seq hr
  have left_eq : List.replicate rightZeros false++false::archive=
      List.replicate (leftZeros+gap+2) false++archive := by
    change List.replicate rightZeros false++(List.replicate 1 false++archive) = _
    rw [zeros_join]
    have hn : rightZeros+1=leftZeros+gap+2 := by dsimp [rightZeros];omega
    rw [hn]
  rw [left_eq] at combined
  have cost : ((leftZeros+2)+2)+(rightZeros+2)≤2*leftZeros+gap+7 := by
    dsimp [rightZeros]
    omega
  simpa [returnOutputMachine,clearMarkerMachine,PSTRTMSeq005.rightLabel,suffix] using combined.mono cost

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticClearInput035
