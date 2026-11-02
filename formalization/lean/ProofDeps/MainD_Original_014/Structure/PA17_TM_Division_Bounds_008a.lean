module
public import Common.PSTR_TM_Trace_002

/-! Pure cost bookkeeping. These inequalities are used only AFTER actual
phase traces have been constructed; no budget is a machine input or oracle. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionBounds008

theorem iteration_sum (n width : Nat) :
    (8*n+9)+(7*width+3)+(4*width+3)+(4*width+3)+(4*width+3)+
      (13*width+6)+(8*n+15) = 16*n+32*width+42 := by ring

def loopBudget (n width : Nat) : Nat :=
  (8*width+6)+n*(16*n+32*width+42)+(8*n+10)

theorem loopBudget_quadratic (n : Nat) : loopBudget n (n+1) ≤ 128*(n+1)^2 := by
  unfold loopBudget
  nlinarith [Nat.zero_le (n^2)]

theorem loop_segments_bound (n width first iterations last : Nat)
    (room : width = n+1) (hf : first ≤ 8*width+6)
    (hi : iterations ≤ n*(16*n+32*width+42)) (hl : last ≤ 8*n+10) :
    first+iterations+last ≤ 128*(n+1)^2 := by
  subst width
  have h := loopBudget_quadratic n
  unfold loopBudget at h
  omega

theorem quotient_postlude_bound (n : Nat) :
    12*(n+1)+13*n+19+128*(n+1)^2 ≤ 256*(n+2)^2 := by
  nlinarith [Nat.zero_le (n^2)]

theorem remainder_postlude_bound (n : Nat) :
    12*n+9*(n+1)+19+128*((n+1)+1)^2 ≤ 256*(n+2)^2 := by
  nlinarith [Nat.zero_le (n^2)]

theorem complete_trace_bound (size n front body output : Nat)
    (room : n+2 ≤ size) (hf : front ≤ 4096*size^2)
    (hb : body ≤ 128*(n+1)^2) (ho : output ≤ 256*(n+2)^2) :
    front+body+output ≤ 8192*size^2 := by
  have hsmall : n+1 ≤ size := by omega
  have hs : (n+1)^2 ≤ size^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hsmall hsmall
  have hr : (n+2)^2 ≤ size^2 := by
    simpa only [pow_two] using Nat.mul_le_mul room room
  nlinarith [Nat.zero_le (size^2)]

theorem original_visitedSpace_bound {states : Nat} (machine : Machine states)
    (inputLength size : Nat) (trace : List (MachineState states))
    (positive : 1 ≤ size) (hin : inputLength ≤ 2*size)
    (ht : trace.length ≤ 8192*size^2) :
    visitedSpace machine inputLength trace ≤ 32768*size^2 := by
  have hs : size ≤ size^2 := by
    simpa only [Nat.mul_one,pow_two] using Nat.mul_le_mul_left size positive
  have hv := PSTRTMTrace002.visitedSpace_le machine inputLength trace
  nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionBounds008
