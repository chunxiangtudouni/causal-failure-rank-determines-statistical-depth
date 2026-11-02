module

public import Paid.PDLower_CoreSearch_Midpoint_002
public import Paid.PDLower_CoreSearch_NumericSegment_018
public import Paid.PDLower_CoreSearch_ScalarNumbers_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

theorem midpoint_evaluated_bits (values : ℕ→Cell) (lower upper : ℚ) (scale budget : ℕ)
    (initial : HeaderValueBits values budget) (lowerValue : values 14=.rational lower) (upperValue : values 15=.rational upper)
    (lowerBits : ratEncodingBits lower≤scale) (upperBits : ratEncodingBits upper≤scale)
    (room : 1+scalarValueBudget scale≤budget) : HeaderEvaluatedBits budget midpointCommands values := by
  let one := Function.update values 39 (.rational (1/2))
  let two := Function.update one 24 (.rational (lower+upper))
  let three := Function.update two 24 (.rational ((lower+upper)/2))
  have half : ratEncodingBits (1/2:ℚ)=4 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have divisor : ratEncodingBits (2:ℚ)=4 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have add := ratEncodingBits_add_le lower upper
  have divide := ratEncodingBits_div_le (lower+upper) (2:ℚ)
  have oneBits : HeaderValueBits one budget := initial.update (by change 1+ratEncodingBits (1/2:ℚ)≤budget;unfold scalarValueBudget at room;omega)
  have twoBits : HeaderValueBits two budget := oneBits.update (by change 1+ratEncodingBits (lower+upper)≤budget;unfold scalarValueBudget at room;omega)
  have threeBits : HeaderValueBits three budget := twoBits.update (by change 1+ratEncodingBits ((lower+upper)/2)≤budget;unfold scalarValueBudget at room;omega)
  refine ⟨one,?_,oneBits,two,?_,twoBits,three,?_,threeBits,True.intro⟩
  all_goals simp [HeaderCommand.eval,one,two,three,lowerValue,upperValue,Cell.rat?,RatOp.eval,div_eq_mul_inv]

/-- Same24 actual midpoint ISA, original total/heap result, all physical
prefixes and full original operands under one fixed caller budget. -/
theorem midpoint_segment_bits (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (lower upper : ℚ) (scale budget : ℕ) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (lowerValue : values 14=.rational lower) (upperValue : values 15=.rational upper)
    (safe : RootD27.Bits.SafeBits before budget) (lowerBits : ratEncodingBits lower≤scale) (upperBits : ratEncodingBits upper≤scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+24)≤budget) (fetched : FetchesCode program before.pc (headerCode midpointCommands)) :
    ∃ after : State,NumericSegment program input before after 375 budget ∧ Header after 0 (midpointValues values lower upper) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+24 ∧ after.register .total=.rational ((lower+upper)/2) ∧
      after.heap 24=.rational ((lower+upper)/2) := by
  have bounded := midpoint_evaluated_bits values lower upper scale budget (HeaderValueBits.of_safe header safe)
    lowerValue upperValue lowerBits upperBits room
  obtain ⟨after,actual,afterHeader,afterFresh,pc,run⟩ :=
    commands_segment_bits midpointCommands program input before values (midpointValues values lower upper) budget
      midpointCommands_valid midpointCommands_targets header fresh (midpointCommands_eval values lower upper lowerValue upperValue)
      safe bounded addressBits (by simpa only [midpointCode_length] using pcBits) fetched
  have direct := midpoint_execute input before values lower upper header fresh lowerValue upperValue
  have equal : after=midpointResult before lower upper := Option.some.inj (run.symm.trans direct)
  have total : after.register .total=.rational ((lower+upper)/2) := equal.symm ▸ midpointResult_total before lower upper
  have value := (afterHeader.value 24 (by decide)).trans (midpointValues_value values lower upper)
  exact ⟨after,by simpa only [midpointCode_length] using actual,afterHeader,afterFresh,
    by simpa only [midpointCode_length] using pc,total,by simpa only [Nat.zero_add] using value⟩

end PDLower.CoreSearch
