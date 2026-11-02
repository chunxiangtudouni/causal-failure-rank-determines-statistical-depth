module
public import Structure.PA17_TM_RatArithmetic_ClearInput_035d

/-! Actual original-bank cleanup followed by the actual return to an
ALREADY PRODUCED output. This is a cleanup component, not an arithmetic
answer supplied to the original machine. The full caller must first prove
that its cache eraser/output producer establishes this intermediate tape. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticClearInput035

open Turing PA17TMRatArithmeticWidth018

def clearAndReturnMachine : Machine 38 :=
  PSTRTMSeq005.seqMachine clearFieldsMachine returnOutputMachine

theorem clear_and_return_bounded (sx : Bool) (archive nx dxTail ny dyTail : List Bool)
    (gap : Nat) (word : List Bool) :
    BoundedRun clearAndReturnMachine
      (Tape.mk₂ archive (prefixRight sx (bank nx (false::dxTail) ny (false::dyTail)
        (List.replicate gap false++true::word)))) 38
      (Tape.mk₂
        (List.replicate (2*bankWidth nx (false::dxTail) ny (false::dyTail)+gap+14) false++archive)
        (true::word))
      (8*bankWidth nx (false::dxTail) ny (false::dyTail)+gap+60) := by
  have hf := clear_fields_bounded sx archive nx dxTail ny dyTail
    (List.replicate gap false++true::word)
  have hr := return_output_bounded (2*bankWidth nx (false::dxTail) ny (false::dyTail)+12) gap archive word
  have combined := hf.seq hr
  have length_eq : (2*bankWidth nx (false::dxTail) ny (false::dyTail)+12)+gap+2=
      2*bankWidth nx (false::dxTail) ny (false::dyTail)+gap+14 := by omega
  rw [length_eq] at combined
  have cost : (4*bankWidth nx (false::dxTail) ny (false::dyTail)+29)+
      (2*(2*bankWidth nx (false::dxTail) ny (false::dyTail)+12)+gap+7) ≤
      8*bankWidth nx (false::dxTail) ny (false::dyTail)+gap+60 := by omega
  simpa [clearAndReturnMachine,PSTRTMSeq005.rightLabel] using combined.mono cost

theorem clear_and_return_contract (sx : Bool) (archive nx dxTail ny dyTail : List Bool)
    (gap : Nat) (word : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom clearAndReturnMachine
      ⟨0,Tape.mk₂ archive (prefixRight sx (bank nx (false::dxTail) ny (false::dyTail)
        (List.replicate gap false++true::word)))⟩ trace
      ⟨38,Tape.mk₂
        (List.replicate (2*bankWidth nx (false::dxTail) ny (false::dyTail)+gap+14) false++archive)
        (true::word)⟩ ∧
      trace.length≤8*bankWidth nx (false::dxTail) ny (false::dyTail)+gap+60 ∧
      ∀ prefixLength inputLength,
        visitedSpace clearAndReturnMachine inputLength (trace.take prefixLength) ≤
          inputLength+16*bankWidth nx (false::dxTail) ny (false::dyTail)+2*gap+121 := by
  obtain ⟨trace,run,timeBound⟩ := clear_and_return_bounded sx archive nx dxTail ny dyTail gap word
  refine ⟨trace,run,timeBound,?_⟩
  intro prefixLength inputLength
  have hs := PSTRTMTrace002.visitedSpace_le clearAndReturnMachine inputLength (trace.take prefixLength)
  have hl : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

theorem left_blank_reserve (n : Nat) (word : List Bool) :
    Tape.mk₂ (List.replicate n false++[false]) word=Tape.mk₁ word := by
  have blank : ListBlank.mk (List.replicate n false++[false])=ListBlank.mk ([] : List Bool) := by
    rw [PSTRTMRawNat010.blank_append_false]
    simpa only [List.nil_append] using PSTRTMPackFinish039.blank_false_suffix [] n
  simp only [Tape.mk₁,Tape.mk₂,blank]

theorem clear_standalone_contract (sx : Bool) (nx dxTail ny dyTail : List Bool) (gap : Nat) (word : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom clearAndReturnMachine
      ⟨0,Tape.mk₂ [false] (prefixRight sx (bank nx (false::dxTail) ny (false::dyTail)
        (List.replicate gap false++true::word)))⟩ trace
      ⟨38,Tape.mk₁ (true::word)⟩ ∧
      trace.length≤8*bankWidth nx (false::dxTail) ny (false::dyTail)+gap+60 ∧
      ∀ prefixLength inputLength,
        visitedSpace clearAndReturnMachine inputLength (trace.take prefixLength) ≤
          inputLength+16*bankWidth nx (false::dxTail) ny (false::dyTail)+2*gap+121 := by
  obtain ⟨trace,run,timeBound,spaceBound⟩ := clear_and_return_contract sx [false] nx dxTail ny dyTail gap word
  refine ⟨trace,?_,timeBound,spaceBound⟩
  simpa only [left_blank_reserve] using run

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticClearInput035
