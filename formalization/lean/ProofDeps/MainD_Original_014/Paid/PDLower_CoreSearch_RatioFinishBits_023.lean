module

public import Paid.PDLower_CoreSearch_PrepareBits_019
public import Paid.PDLower_CoreSearch_LiteralBits_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

theorem mixtureRatio_segment_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (scale budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (numerator : values 41=.rational (P.certificate.risk-P.solveRisk upper))
    (denominator : values 30=.rational (P.solveRisk lower-P.solveRisk upper))
    (nonzero : P.solveRisk lower-P.solveRisk upper≠0) (safe : RootD27.Bits.SafeBits before budget)
    (intrinsic : ScalarInputBits P fee lower upper scale) (room : 1+scalarValueBudget scale≤budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+10)≤budget)
    (fetched : FetchesCode program before.pc (headerCode mixtureRatioCommands)) :
    ∃ after : State,NumericSegment program input before after 165 budget ∧
      Header after 0 (Function.update values 31 (.rational (P.mixtureWeight lower upper))) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+10 := by
  let next := Function.update values 31 (.rational (P.mixtureWeight lower upper))
  have numbers := scalarArithmetic_bits P fee lower upper scale intrinsic
  have weightBits := numbers.weight
  have nextBits : HeaderValueBits next budget := (HeaderValueBits.of_safe header safe).update
    (by change 1+ratEncodingBits (P.mixtureWeight lower upper)≤budget;omega)
  have evaluated : headerEval mixtureRatioCommands values=some next := by
    simp [mixtureRatioCommands,headerEval,HeaderCommand.eval,Cell.rat?,RatOp.eval,numerator,denominator,nonzero,mixtureWeight,next]
  have bounded : HeaderEvaluatedBits budget mixtureRatioCommands values := by
    refine ⟨next,?_,nextBits,True.intro⟩
    simp [HeaderCommand.eval,Cell.rat?,RatOp.eval,numerator,denominator,nonzero,mixtureWeight,next]
  obtain ⟨after,actual,afterHeader,afterFresh,pc,_run⟩ :=
    commands_segment_bits mixtureRatioCommands program input before values next budget mixtureRatio_valid mixtureRatio_targets header fresh
      evaluated safe bounded addressBits (by simpa only [mixtureRatio_length] using pcBits) fetched
  exact ⟨after,by simpa only [mixtureRatio_length] using actual,afterHeader,afterFresh,
    by simpa only [mixtureRatio_length] using pc⟩

theorem mixtureZero_segment_bits (P : Parameters) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (zero : P.solveRisk lower-P.solveRisk upper=0) (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+4)≤budget)
    (fetched : FetchesCode program before.pc (headerCode mixtureZeroCommands)) :
    ∃ after : State,NumericSegment program input before after 75 budget ∧
      Header after 0 (Function.update values 31 (.rational (P.mixtureWeight lower upper))) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+4 := by
  have same : P.mixtureWeight lower upper=0 := by simp [mixtureWeight,zero]
  have valueBits : (.rational (0:ℚ) : Cell).bits≤budget := by
    norm_num [Cell.bits,ratEncodingBits,ratNumBits,ratDenBits,natBits]
    omega
  obtain ⟨after,actual,afterHeader,afterFresh,pc⟩ := literal_segment_bits program input before values 31 budget (.rational 0)
    (by decide) header fresh safe valueBits addressBits pcBits fetched
  exact ⟨after,actual,by simpa only [same] using afterHeader,afterFresh,pc⟩

theorem mixtureFinish_evaluated_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (values : ℕ→Cell) (scale budget : ℕ) (initial : HeaderValueBits values budget)
    (ratio : values 31=.rational (P.mixtureWeight lower upper))
    (lowerCost : values 32=.rational (P.solveCost fee lower)) (upperCost : values 33=.rational (P.solveCost fee upper))
    (intrinsic : ScalarInputBits P fee lower upper scale) (room : 1+scalarValueBudget scale≤budget) :
    HeaderEvaluatedBits budget mixtureFinishCommands values := by
  have numbers := scalarArithmetic_bits P fee lower upper scale intrinsic
  have lift (q : ℚ) (bounded : ratEncodingBits q≤scalarValueBudget scale) : (.rational q : Cell).bits≤budget := by
    change 1+ratEncodingBits q≤budget
    omega
  let one := Function.update values 41 (.rational 1)
  let two := Function.update one 41 (.rational (1-P.mixtureWeight lower upper))
  let three := Function.update two 34 (.rational ((1-P.mixtureWeight lower upper)*P.solveCost fee upper))
  let four := Function.update three 35 (.rational (P.mixtureWeight lower upper*P.solveCost fee lower))
  let five := Function.update four 36 (.rational (P.mixtureCost fee lower upper))
  let six := Function.update five 39 (.rational (1/2))
  let seven := Function.update six 41 (.rational (P.mixtureCost fee lower upper/2))
  have oneBits : HeaderValueBits one budget := initial.update (lift _ numbers.one)
  have twoBits : HeaderValueBits two budget := oneBits.update (lift _ numbers.complement)
  have threeBits : HeaderValueBits three budget := twoBits.update (lift _ numbers.weightedUpper)
  have fourBits : HeaderValueBits four budget := threeBits.update (lift _ numbers.weightedLower)
  have fiveBits : HeaderValueBits five budget := fourBits.update (lift _ numbers.mixture)
  have sixBits : HeaderValueBits six budget := fiveBits.update (lift _ numbers.half)
  have sevenBits : HeaderValueBits seven budget := sixBits.update (lift _ numbers.halfMixture)
  refine ⟨one,?_,oneBits,two,?_,twoBits,three,?_,threeBits,four,?_,fourBits,five,?_,fiveBits,six,?_,sixBits,seven,?_,sevenBits,True.intro⟩
  all_goals simp [HeaderCommand.eval,one,two,three,four,five,six,seven,ratio,lowerCost,upperCost,Cell.rat?,RatOp.eval,mixtureCost,div_eq_mul_inv]

theorem mixtureFinish_segment_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (scale budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (ratio : values 31=.rational (P.mixtureWeight lower upper))
    (lowerCost : values 32=.rational (P.solveCost fee lower)) (upperCost : values 33=.rational (P.solveCost fee upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+58)≤budget) (fetched : FetchesCode program before.pc (headerCode mixtureFinishCommands)) :
    ∃ after : State,NumericSegment program input before after 885 budget ∧
      Header after 0 (mixtureFinishValues P fee lower upper values) ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+58 := by
  have bounded := mixtureFinish_evaluated_bits P fee lower upper values scale budget (HeaderValueBits.of_safe header safe)
    ratio lowerCost upperCost intrinsic room
  obtain ⟨after,actual,afterHeader,afterFresh,pc,_run⟩ :=
    commands_segment_bits mixtureFinishCommands program input before values (mixtureFinishValues P fee lower upper values) budget
      mixtureFinish_valid mixtureFinish_targets header fresh (mixtureFinish_eval P fee lower upper values ratio lowerCost upperCost)
      safe bounded addressBits (by simpa only [mixtureFinish_length] using pcBits) fetched
  exact ⟨after,by simpa only [mixtureFinish_length] using actual,afterHeader,afterFresh,
    by simpa only [mixtureFinish_length] using pc⟩

end PDLower.CoreSearch
