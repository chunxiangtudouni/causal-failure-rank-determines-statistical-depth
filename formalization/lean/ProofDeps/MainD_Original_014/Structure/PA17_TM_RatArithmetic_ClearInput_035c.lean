module
public import Structure.PA17_TM_RatArithmetic_ClearInput_035b
public import Structure.PA17_TM_RatArithmetic_Width_018i

/-! Clear the original four fields by actual streaming erasers. Keep only
the first original header TRUE as a real return marker. The arbitrary suffix
after the old FALSE footer, including a later output, is never inspected. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticClearInput035

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002

def firstPairMachine : Machine 21 := PSTRTMSeq005.seqMachine headerMachine pairEraseMachine
def throughYMachine : Machine 24 := PSTRTMSeq005.seqMachine firstPairMachine headerRightMachine
def clearFieldsMachine : Machine 32 := PSTRTMSeq005.seqMachine throughYMachine pairEraseMachine

theorem clear_fields_bounded (sx : Bool) (archive nx dxTail ny dyTail suffix : List Bool) :
    BoundedRun clearFieldsMachine
      (Tape.mk₂ archive (prefixRight sx (bank nx (false::dxTail) ny (false::dyTail) suffix))) 31
      (Tape.mk₂
        (List.replicate (2*bankWidth nx (false::dxTail) ny (false::dyTail)+12) false++true::archive)
        (false::suffix))
      (4*bankWidth nx (false::dxTail) ny (false::dyTail)+29) := by
  let wordY := pairWord ny dyTail suffix
  let word := bank nx (false::dxTail) ny (false::dyTail) suffix
  let headerLeft := List.replicate 6 false++true::archive
  let pairWidthX := nx.length+(false::dxTail).length
  let pairWidthY := ny.length+(false::dyTail).length
  let leftX := List.replicate (2*pairWidthX+2) false++headerLeft
  have word_eq : word=pairWord nx dxTail (false::wordY) := rfl
  have hh : BoundedRun headerMachine (Tape.mk₂ archive (prefixRight sx word)) 13
      (Tape.mk₂ headerLeft word) 14 := by
    refine ⟨headerTrace true false false true sx false archive word,?_,?_⟩
    · simpa only [prefixRight,headerLeft,headerState,List.cons_append,List.nil_append] using
        header_runsFrom true false false true sx false archive word
    · rw [header_length]
  have hx : BoundedRun pairEraseMachine (Tape.mk₂ headerLeft word) 6
      (Tape.mk₂ leftX (false::false::wordY)) (4*pairWidthX+6) := by
    simpa only [word_eq,leftX,pairWidthX] using pair_erase_bounded headerLeft nx dxTail (false::wordY)
  have hy : BoundedRun headerRightMachine (Tape.mk₂ leftX (false::false::wordY)) 2
      (Tape.mk₂ (false::false::leftX) wordY) 3 :=
    ⟨headerRightTrace leftX false false wordY,headerRight_runsFrom leftX false false wordY,by rfl⟩
  have ht := pair_erase_bounded (false::false::leftX) ny dyTail suffix
  have combined := ((hh.seq hx).seq hy).seq ht
  have left_eq : List.replicate (2*pairWidthY+2) false++(false::false::leftX)=
      List.replicate (2*bankWidth nx (false::dxTail) ny (false::dyTail)+12) false++true::archive := by
    change List.replicate (2*pairWidthY+2) false++
      (List.replicate 2 false++(List.replicate (2*pairWidthX+2) false++
        (List.replicate 6 false++true::archive))) = _
    rw [zeros_join,zeros_join,zeros_join]
    have hn : ((2*pairWidthY+2)+2+(2*pairWidthX+2))+6 =
        2*bankWidth nx (false::dxTail) ny (false::dyTail)+12 := by
      dsimp [pairWidthX,pairWidthY,bankWidth]
      omega
    rw [hn]
  have cost : ((14+(4*pairWidthX+6))+3)+(4*pairWidthY+6) ≤
      4*bankWidth nx (false::dxTail) ny (false::dyTail)+29 := by
    dsimp [pairWidthX,pairWidthY,bankWidth]
    omega
  rw [left_eq] at combined
  simpa [clearFieldsMachine,throughYMachine,firstPairMachine,PSTRTMSeq005.rightLabel,
    word,wordY,pairWidthY] using combined.mono cost

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticClearInput035
