module
public import Structure.PA17_TM_RatArithmetic_ClearInput_035a
public import Structure.PA17_TM_RatArithmetic_Cleanup_026b
public import Structure.PA17_TM_RatArithmetic_Width_018f

/-! Reuse the actual four-label field eraser twice. The first field's
second OWN cell is the physically clamped FALSE first DATA of the second
field; the second field really starts there. No separator is deleted. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticClearInput035

open Turing PA17TMRatArithmeticCleanup026 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002

def pairEraseMachine : Machine 7 := PSTRTMSeq005.seqMachine fieldEraseMachine fieldEraseMachine

def pairWord (first secondTail suffix : List Bool) : List Bool :=
  nxStream first (nxStream (false::secondTail) (false::suffix))

theorem zeros_join (a b : Nat) (archive : List Bool) :
    List.replicate a false++(List.replicate b false++archive)=List.replicate (a+b) false++archive := by
  rw [List.replicate_add,List.append_assoc]

theorem pair_erase_bounded (archive first secondTail suffix : List Bool) :
    BoundedRun pairEraseMachine (Tape.mk₂ archive (pairWord first secondTail suffix)) 6
      (Tape.mk₂ (List.replicate (2*(first.length+(false::secondTail).length)+2) false++archive)
        (false::suffix)) (4*(first.length+(false::secondTail).length)+6) := by
  let second := false::secondTail
  let middleLeft := List.replicate (2*first.length+1) false++archive
  have hf : BoundedRun fieldEraseMachine (Tape.mk₂ archive (pairWord first secondTail suffix)) 2
      (Tape.mk₂ middleLeft (nxStream second (false::suffix))) (4*first.length+3) := by
    refine ⟨fieldTrace archive first
      (true::(PSTRTMIncrement009.blocks secondTail++false::false::suffix)),?_,?_⟩
    · simpa only [pairWord,nxStream,second,middleLeft,fieldState,fieldFinal,
        PSTRTMIncrement009.blocks,List.flatMap_cons,List.flatMap_nil,List.cons_append,
        List.nil_append,List.append_assoc] using
        field_runsFrom archive first (true::(PSTRTMIncrement009.blocks secondTail++false::false::suffix))
    · rw [fieldTrace_length]
  have hs : BoundedRun fieldEraseMachine (Tape.mk₂ middleLeft (nxStream second (false::suffix))) 2
      (Tape.mk₂ (List.replicate (2*second.length+1) false++middleLeft) (false::suffix))
      (4*second.length+3) := by
    refine ⟨fieldTrace middleLeft second suffix,?_,?_⟩
    · simpa only [nxStream,fieldState,fieldFinal] using field_runsFrom middleLeft second suffix
    · rw [fieldTrace_length]
  have combined := hf.seq hs
  have he : List.replicate (2*second.length+1) false++middleLeft =
      List.replicate (2*(first.length+second.length)+2) false++archive := by
    dsimp only [middleLeft]
    rw [zeros_join]
    have hn : (2*second.length+1)+(2*first.length+1)=2*(first.length+second.length)+2 := by omega
    rw [hn]
  have hc : (4*first.length+3)+(4*second.length+3)≤4*(first.length+second.length)+6 := by omega
  rw [he] at combined
  simpa [pairEraseMachine,PSTRTMSeq005.rightLabel,second] using combined.mono hc

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticClearInput035
