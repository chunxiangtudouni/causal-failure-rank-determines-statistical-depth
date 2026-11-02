module

public import Paid.PDLower_CoreSearch_ScalarNumbers_017
public import Paid.PDLower_CoreSearch_NumericSegment_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

theorem mixturePrepare_evaluated_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (values : ℕ→Cell) (scale budget : ℕ) (initial : HeaderValueBits values budget)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (intrinsic : ScalarInputBits P fee lower upper scale) (room : 1+scalarValueBudget scale≤budget) :
    HeaderEvaluatedBits budget mixturePrepareCommands values := by
  have numbers := scalarArithmetic_bits P fee lower upper scale intrinsic
  have lift (q : ℚ) (bounded : ratEncodingBits q≤scalarValueBudget scale) : (.rational q : Cell).bits≤budget := by
    change 1+ratEncodingBits q≤budget
    omega
  let one := Function.update values 30 (.rational (P.solveRisk lower-P.solveRisk upper))
  let two := Function.update one 41 (.rational (P.certificate.risk-P.solveRisk upper))
  let three := Function.update two 32 (.rational (fee*(P.solveRecord lower).repairs))
  let four := Function.update three 32 (.rational (P.solveCost fee lower))
  let five := Function.update four 33 (.rational (fee*(P.solveRecord upper).repairs))
  let six := Function.update five 33 (.rational (P.solveCost fee upper))
  let seven := Function.update six 37 (.rational (upper.multiplier-lower.multiplier))
  let eight := Function.update seven 38 (.rational ((upper.multiplier-lower.multiplier)*P.certificate.risk))
  let nine := Function.update eight 39 (.rational (1/2))
  have oneBits : HeaderValueBits one budget := initial.update (lift _ numbers.denominator)
  have twoBits : HeaderValueBits two budget := oneBits.update (lift _ numbers.numerator)
  have threeBits : HeaderValueBits three budget := twoBits.update (lift _ numbers.lowerProduct)
  have fourBits : HeaderValueBits four budget := threeBits.update (lift _ numbers.lowerCost)
  have fiveBits : HeaderValueBits five budget := fourBits.update (lift _ numbers.upperProduct)
  have sixBits : HeaderValueBits six budget := fiveBits.update (lift _ numbers.upperCost)
  have sevenBits : HeaderValueBits seven budget := sixBits.update (lift _ numbers.width)
  have eightBits : HeaderValueBits eight budget := sevenBits.update (lift _ numbers.gap)
  have nineBits : HeaderValueBits nine budget := eightBits.update (lift _ numbers.half)
  refine ⟨one,?_,oneBits,two,?_,twoBits,three,?_,threeBits,four,?_,fourBits,five,?_,fiveBits,six,?_,sixBits,
    seven,?_,sevenBits,eight,?_,eightBits,nine,?_,nineBits,True.intro⟩
  all_goals simp [HeaderCommand.eval,one,two,three,four,five,six,seven,eight,nine,
    risk,feeValue,lowerPrice,upperPrice,lowerObs,lowerRep,lowerRisk,upperObs,upperRep,upperRisk,Cell.rat?,RatOp.eval,solveCost]

theorem mixturePrepare_segment_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (scale budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+84)≤budget) (fetched : FetchesCode program before.pc (headerCode mixturePrepareCommands)) :
    ∃ after : State,NumericSegment program input before after 1275 budget ∧
      Header after 0 (mixturePrepareValues P fee lower upper values) ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+84 := by
  have bounded := mixturePrepare_evaluated_bits P fee lower upper values scale budget (HeaderValueBits.of_safe header safe)
    risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk upperObs upperRep upperRisk intrinsic room
  obtain ⟨after,actual,afterHeader,afterFresh,pc,_run⟩ :=
    commands_segment_bits mixturePrepareCommands program input before values (mixturePrepareValues P fee lower upper values) budget
      mixturePrepareCommands_valid mixturePrepareCommands_targets header fresh
      (mixturePrepareCommands_eval P fee lower upper values risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk upperObs upperRep upperRisk)
      safe bounded addressBits (by simpa only [mixturePrepareCode_length] using pcBits) fetched
  exact ⟨after,by simpa only [mixturePrepareCode_length] using actual,afterHeader,afterFresh,
    by simpa only [mixturePrepareCode_length] using pc⟩

end PDLower.CoreSearch
