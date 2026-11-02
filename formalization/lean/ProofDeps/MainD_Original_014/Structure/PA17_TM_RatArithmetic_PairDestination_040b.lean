module
public import Structure.PA17_TM_RatArithmetic_PairDestination_040a

/-! Actual round trip through the shared B DATA/A OWN cell. This retains
the entire existing A field and arbitrary partial B copy, not just values.
It is a destination connector, not a two-operand loader or scalar machine. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairDestination040

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002

theorem bounded_prefix_contract {s : Nat} {machine : Machine s}
    {input output : Tape Bool} {q : Fin (s+1)} {bound : Nat}
    (run : BoundedRun machine input q output bound) :
    ∃ trace, PSTRTMSeq005.RunsFrom machine ⟨0,input⟩ trace ⟨q,output⟩ ∧
      trace.length≤bound ∧ ∀ prefixLength inputLength,
        visitedSpace machine inputLength (trace.take prefixLength) ≤ inputLength+2*bound+1 := by
  obtain ⟨trace,hr,ht⟩ := run
  refine ⟨trace,hr,ht,?_⟩
  intro prefixLength inputLength
  have hs := PSTRTMTrace002.visitedSpace_le machine inputLength (trace.take prefixLength)
  have hl : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

def roundBeforeBackMachine : Machine 8 := PSTRTMSeq005.seqMachine outToBMachine backOneMachine

def roundMachine : Machine 21 := PSTRTMSeq005.seqMachine roundBeforeBackMachine backFromBMachine

def workTape (archive digits bTail : List Bool) (gap : Nat) : Tape Bool :=
  Tape.mk₂ archive (true::(List.replicate gap false++true::false::
    (PSTRTMIncrement009.blocks digits++false::false::bTail)))

theorem round_bounded (archive digits bTail : List Bool) (gap : Nat) :
    BoundedRun roundMachine (workTape archive digits bTail gap) 21
      (workTape archive digits bTail gap) (2*gap+4*digits.length+21) := by
  have ho := out_to_B_bounded true archive digits bTail gap
  let aLeft := PSTRTMRawNat010.leftBlocks digits.reverse++false::true::
    (List.replicate gap false++true::archive)
  have hl : BoundedRun backOneMachine (Tape.mk₂ (false::aLeft) (false::bTail)) 1
      (Tape.mk₂ aLeft (false::false::bTail)) 2 :=
    ⟨backOneTrace aLeft false (false::bTail),backOne_runsFrom aLeft false (false::bTail),by rfl⟩
  have hb := back_from_B_bounded archive digits bTail gap
  have combined := (ho.seq hl).seq hb
  have cost : ((gap+2*digits.length+7)+2)+(gap+2*digits.length+12)≤
      2*gap+4*digits.length+21 := by omega
  simpa [roundMachine,roundBeforeBackMachine,PSTRTMSeq005.rightLabel,workTape,aLeft] using
    combined.mono cost

theorem round_contract (archive digits bTail : List Bool) (gap : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom roundMachine
      ⟨0,workTape archive digits bTail gap⟩ trace ⟨21,workTape archive digits bTail gap⟩ ∧
      trace.length≤2*gap+4*digits.length+21 ∧ ∀ prefixLength inputLength,
        visitedSpace roundMachine inputLength (trace.take prefixLength)≤
          inputLength+4*gap+8*digits.length+43 := by
  obtain ⟨trace,hr,ht,hs⟩ := bounded_prefix_contract (round_bounded archive digits bTail gap)
  refine ⟨trace,hr,ht,?_⟩
  intro prefixLength inputLength
  have bound := hs prefixLength inputLength
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairDestination040
