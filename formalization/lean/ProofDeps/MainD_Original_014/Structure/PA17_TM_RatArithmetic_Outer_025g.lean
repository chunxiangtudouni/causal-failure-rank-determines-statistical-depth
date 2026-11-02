module
public import Structure.PA17_TM_RatArithmetic_Outer_025f
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023k

/-! Concrete original-input allocator instance. This module MUST NOT be
checked/frozen until the actual023 plain-pass parent is fully frozen. The
body premise of025b-f is discharged here by that actual closed machine. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014

theorem original_body_contract (k : Nat) :
    BodyRunContract (PA17TMRatArithmeticAllocatePass023.passMachine k) k := by
  intro x y h n
  obtain ⟨trace,run,timeBound⟩ :=
    PA17TMRatArithmeticAllocatePass023.original_pass_bounded k h n x y
  refine ⟨trace,?_,?_⟩
  · simpa only [popNxFound,popNxInitial,blockCfg_tape,sevenState,
      ROOTTMGCDPop016.state,prefixLeft,nxContext,ROOTTMGCDPop016.ones,ROOTTMGCDCounter011.ones,
      List.cons_append,List.nil_append,bankAt,PA17TMRatArithmeticAllocatePass023.gapTail] using run
  · simpa only [passFee,PA17TMRatArithmeticAllocatePass023.passFee] using timeBound

/-- k is a fixed code constant before every original rational operand.
This is the allocator, not a whole arithmetic operation or a source loader. -/
theorem original_allocator_exists (k : Nat) :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ trace final,
        Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=Tape.mk₂ [false]
          (prefixRight (sign x) (bankAt x y (k*(fieldWidth x y)^2))) ∧
        final.q.val=(mNx x y).val*(rawLoopCapacity (PA17TMRatArithmeticAllocatePass023.passCap k)+1)+
          (rawLoopCapacity (PA17TMRatArithmeticAllocatePass023.passCap k)+1)+7 ∧
        trace.length≤c*((encode [.rational x,.rational y]).length+1)^d ∧
        ∀ prefixLength,
          visitedSpace program (encode [.rational x,.rational y]).length (trace.take prefixLength) ≤
            c*((encode [.rational x,.rational y]).length+1)^d :=
  allocation_code_of_body (PA17TMRatArithmeticAllocatePass023.passMachine k) k (original_body_contract k)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025
