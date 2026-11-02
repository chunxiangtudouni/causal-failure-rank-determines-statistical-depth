module

public import Paid.PDROC_BitVM_VM_BoolCompose_Actual_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.VM.BoolCompose

open PaperProofs.Paid.Computation

variable {a b c : ℕ}

theorem visited_eq_original (code : BitMachine a) (inputLength : ℕ) (states : List (BitState a)) :
    visitedBitSpace code inputLength states=PaperProofs.Common.Native.RationalControllerComputation.visitedSpace code inputLength states := rfl

/-- Every actual prefix uses the original absolute input interval and
physical displacements; no phase-local restart of visited space occurs. -/
theorem every_prefix_visited (code : BitMachine a) (inputLength : ℕ)
    (states : List (BitState a)) (bound : ℕ) (cost : states.length≤bound) :
    ∀ count,visitedBitSpace code inputLength (states.take count)≤ inputLength+2*bound+1 := by
  intro count
  rw [visited_eq_original]
  have actual := PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrace002.visitedSpace_le code inputLength (states.take count)
  have taken : (states.take count).length≤states.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

theorem actual_two_with_resources (first : BitMachine a) (second : BitMachine b) (input : List Bool)
    (finalFirst : BitState a) (finalSecond : BitState b)
    (statesFirst : List (BitState a)) (statesSecond : List (BitState b)) (firstCost secondCost : ℕ)
    (left : BitRuns first input statesFirst finalFirst)
    (right : PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom second ⟨0,finalFirst.Tape⟩ statesSecond finalSecond)
    (leftCost : statesFirst.length≤firstCost) (rightCost : statesSecond.length≤secondCost) :
    ∃ states final,BitRuns (machine first second) input states final ∧
      final.Tape=finalSecond.Tape ∧ states.length≤firstCost+secondCost ∧
      ∀ count,visitedBitSpace (machine first second) input.length (states.take count)≤
        input.length+2*(firstCost+secondCost)+1 := by
  have cost : (trace statesFirst statesSecond).length≤firstCost+secondCost := by
    rw [trace_length]
    omega
  exact ⟨trace statesFirst statesSecond,PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.rightCfg (a:=a) finalSecond,
    actual_run first second input finalFirst finalSecond statesFirst statesSecond left right,rfl,cost,
    every_prefix_visited (machine first second) input.length _ _ cost⟩

theorem actual_three_with_resources (first : BitMachine a) (second : BitMachine b) (third : BitMachine c)
    (input : List Bool) (finalFirst : BitState a) (finalSecond : BitState b) (finalThird : BitState c)
    (statesFirst : List (BitState a)) (statesSecond : List (BitState b)) (statesThird : List (BitState c))
    (firstCost secondCost thirdCost : ℕ)
    (left : BitRuns first input statesFirst finalFirst)
    (middle : PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom second ⟨0,finalFirst.Tape⟩ statesSecond finalSecond)
    (right : PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom third ⟨0,finalSecond.Tape⟩ statesThird finalThird)
    (leftCost : statesFirst.length≤firstCost) (middleCost : statesSecond.length≤secondCost)
    (rightCost : statesThird.length≤thirdCost) :
    ∃ states final,BitRuns (machine (machine first second) third) input states final ∧
      final.Tape=finalThird.Tape ∧ states.length≤firstCost+secondCost+thirdCost ∧
      ∀ count,visitedBitSpace (machine (machine first second) third) input.length (states.take count)≤
        input.length+2*(firstCost+secondCost+thirdCost)+1 := by
  have cost : (trace (trace statesFirst statesSecond) statesThird).length≤firstCost+secondCost+thirdCost := by
    rw [trace_length,trace_length]
    omega
  exact ⟨trace (trace statesFirst statesSecond) statesThird,PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.rightCfg (a:=a+b+1) finalThird,
    actual_three_run first second third input finalFirst finalSecond finalThird statesFirst statesSecond statesThird
      left middle right,rfl,cost,
    every_prefix_visited (machine (machine first second) third) input.length _ _ cost⟩

end PDROC.BitVM.VM.BoolCompose
