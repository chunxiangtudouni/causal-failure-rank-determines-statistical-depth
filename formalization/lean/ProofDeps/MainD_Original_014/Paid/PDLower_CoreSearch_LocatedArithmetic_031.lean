module
public import Paid.PDLower_CoreSearch_LocatedLiterals_030
public import Paid.PDLower_CoreSearch_PrepareBits_019
public import Paid.PDLower_CoreSearch_MidpointBits_020
public import Paid.PDLower_CoreSearch_RatioFinishBits_023
public import Paid.PDLower_CoreSearch_CompareBits_021
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
@[expose] public section
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
namespace PDLower.CoreSearch.Located

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
    (pcBits : natBits (before.pc+84)≤budget) (fetched : FetchesCode program before.pc (headerCode mixturePrepareCommands))
    (low high : ℕ) (pcLower : low≤before.pc) (pcUpper : before.pc+84≤high) :
    ∃ after : State,LocatedSegment program input before after 1275 budget low high ∧
      Header after 0 (mixturePrepareValues P fee lower upper values) ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+84 := by
  have bounded := mixturePrepare_evaluated_bits P fee lower upper values scale budget (HeaderValueBits.of_safe header safe)
    risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk upperObs upperRep upperRisk intrinsic room
  obtain ⟨after,actual,afterHeader,afterFresh,pc,_run⟩ :=
    LocatedSegment.commands mixturePrepareCommands program input before values (mixturePrepareValues P fee lower upper values) budget
      mixturePrepareCommands_valid mixturePrepareCommands_targets header fresh
      (mixturePrepareCommands_eval P fee lower upper values risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk upperObs upperRep upperRisk)
      safe bounded addressBits (by simpa only [mixturePrepareCode_length] using pcBits) fetched low high pcLower (by simpa only [mixturePrepareCode_length] using pcUpper)
  exact ⟨after,by simpa only [mixturePrepareCode_length] using actual,afterHeader,afterFresh,
    by simpa only [mixturePrepareCode_length] using pc⟩


theorem midpoint_segment_bits (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (lower upper : ℚ) (scale budget : ℕ) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (lowerValue : values 14=.rational lower) (upperValue : values 15=.rational upper)
    (safe : RootD27.Bits.SafeBits before budget) (lowerBits : ratEncodingBits lower≤scale) (upperBits : ratEncodingBits upper≤scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+24)≤budget) (fetched : FetchesCode program before.pc (headerCode midpointCommands))
    (low high : ℕ) (pcLower : low≤before.pc) (pcUpper : before.pc+24≤high) :
    ∃ after : State,LocatedSegment program input before after 375 budget low high ∧ Header after 0 (midpointValues values lower upper) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+24 ∧ after.register .total=.rational ((lower+upper)/2) ∧
      after.heap 24=.rational ((lower+upper)/2) := by
  have bounded := midpoint_evaluated_bits values lower upper scale budget (HeaderValueBits.of_safe header safe)
    lowerValue upperValue lowerBits upperBits room
  obtain ⟨after,actual,afterHeader,afterFresh,pc,run⟩ :=
    LocatedSegment.commands midpointCommands program input before values (midpointValues values lower upper) budget
      midpointCommands_valid midpointCommands_targets header fresh (midpointCommands_eval values lower upper lowerValue upperValue)
      safe bounded addressBits (by simpa only [midpointCode_length] using pcBits) fetched low high pcLower (by simpa only [midpointCode_length] using pcUpper)
  have direct := midpoint_execute input before values lower upper header fresh lowerValue upperValue
  have equal : after=midpointResult before lower upper := Option.some.inj (run.symm.trans direct)
  have total : after.register .total=.rational ((lower+upper)/2) := equal.symm ▸ midpointResult_total before lower upper
  have value := (afterHeader.value 24 (by decide)).trans (midpointValues_value values lower upper)
  exact ⟨after,by simpa only [midpointCode_length] using actual,afterHeader,afterFresh,
    by simpa only [midpointCode_length] using pc,total,by simpa only [Nat.zero_add] using value⟩


theorem mixtureRatio_segment_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (scale budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (numerator : values 41=.rational (P.certificate.risk-P.solveRisk upper))
    (denominator : values 30=.rational (P.solveRisk lower-P.solveRisk upper))
    (nonzero : P.solveRisk lower-P.solveRisk upper≠0) (safe : RootD27.Bits.SafeBits before budget)
    (intrinsic : ScalarInputBits P fee lower upper scale) (room : 1+scalarValueBudget scale≤budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+10)≤budget)
    (fetched : FetchesCode program before.pc (headerCode mixtureRatioCommands))
    (low high : ℕ) (pcLower : low≤before.pc) (pcUpper : before.pc+10≤high) :
    ∃ after : State,LocatedSegment program input before after 165 budget low high ∧
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
    LocatedSegment.commands mixtureRatioCommands program input before values next budget mixtureRatio_valid mixtureRatio_targets header fresh
      evaluated safe bounded addressBits (by simpa only [mixtureRatio_length] using pcBits) fetched low high pcLower (by simpa only [mixtureRatio_length] using pcUpper)
  exact ⟨after,by simpa only [mixtureRatio_length] using actual,afterHeader,afterFresh,
    by simpa only [mixtureRatio_length] using pc⟩


theorem mixtureZero_segment_bits (P : Parameters) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (zero : P.solveRisk lower-P.solveRisk upper=0) (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+4)≤budget)
    (fetched : FetchesCode program before.pc (headerCode mixtureZeroCommands))
    (low high : ℕ) (pcLower : low≤before.pc) (pcUpper : before.pc+4≤high) :
    ∃ after : State,LocatedSegment program input before after 75 budget low high ∧
      Header after 0 (Function.update values 31 (.rational (P.mixtureWeight lower upper))) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+4 := by
  have same : P.mixtureWeight lower upper=0 := by simp [mixtureWeight,zero]
  have valueBits : (.rational (0:ℚ) : Cell).bits≤budget := by
    norm_num [Cell.bits,ratEncodingBits,ratNumBits,ratDenBits,natBits]
    omega
  obtain ⟨after,actual,afterHeader,afterFresh,pc⟩ := literal_segment_bits program input before values 31 budget (.rational 0)
    (by decide) header fresh safe valueBits addressBits pcBits fetched low high pcLower pcUpper
  exact ⟨after,actual,by simpa only [same] using afterHeader,afterFresh,pc⟩


theorem mixtureFinish_segment_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (scale budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (ratio : values 31=.rational (P.mixtureWeight lower upper))
    (lowerCost : values 32=.rational (P.solveCost fee lower)) (upperCost : values 33=.rational (P.solveCost fee upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+58)≤budget) (fetched : FetchesCode program before.pc (headerCode mixtureFinishCommands))
    (low high : ℕ) (pcLower : low≤before.pc) (pcUpper : before.pc+58≤high) :
    ∃ after : State,LocatedSegment program input before after 885 budget low high ∧
      Header after 0 (mixtureFinishValues P fee lower upper values) ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+58 := by
  have bounded := mixtureFinish_evaluated_bits P fee lower upper values scale budget (HeaderValueBits.of_safe header safe)
    ratio lowerCost upperCost intrinsic room
  obtain ⟨after,actual,afterHeader,afterFresh,pc,_run⟩ :=
    LocatedSegment.commands mixtureFinishCommands program input before values (mixtureFinishValues P fee lower upper values) budget
      mixtureFinish_valid mixtureFinish_targets header fresh (mixtureFinish_eval P fee lower upper values ratio lowerCost upperCost)
      safe bounded addressBits (by simpa only [mixtureFinish_length] using pcBits) fetched low high pcLower (by simpa only [mixtureFinish_length] using pcUpper)
  exact ⟨after,by simpa only [mixtureFinish_length] using actual,afterHeader,afterFresh,
    by simpa only [mixtureFinish_length] using pc⟩


theorem comparisonStored_segment_bits (comparison : Comparison) (left right : ℕ) (x y : ℚ)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : values left=.rational x) (rightValue : values right=.rational y) (fresh : before.register .fresh=.natural 0)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+10)≤budget) (fetched : FetchesCode program before.pc (comparisonStoredCode comparison left right))
    (low high : ℕ) (pcLower : low≤before.pc) (pcUpper : before.pc+10≤high) :
    LocatedSegment program input before (comparisonStoredResult before left right (comparison.rat x y)) 165 budget low high ∧
      Header (comparisonStoredResult before left right (comparison.rat x y)) 0
        (Function.update values 40 (.natural (if comparison.rat x y then 1 else 0))) := by
  let after := comparisonStoredResult before left right (comparison.rat x y)
  have run := comparisonStored_execute comparison left right x y input before values header leftInside rightInside leftValue rightValue fresh
  have prefixSafe := PDLower.CoreSearch.comparisonStored_prefix_safe comparison left right x y input before values budget header leftInside rightInside
    leftValue rightValue fresh safe small addressBits pcBits
  have actual := LocatedSegment.linear program input (comparisonStoredCode comparison left right) before after budget
    (comparisonStored_straight comparison left right) fetched run
    (fun count bounded state executed => comparisonStored_prefix_memory comparison left right x y input before state values header leftInside rightInside
      leftValue rightValue fresh count (by simpa only [comparisonStored_length] using bounded) executed)
    prefixSafe low high pcLower (by simpa only [comparisonStored_length] using pcUpper)
  have fields := comparisonStored_fields before left right (comparison.rat x y)
  have afterHeader : Header after 0 (Function.update values 40 (.natural (if comparison.rat x y then 1 else 0))) :=
    header.update 40 _ fields.1 (by rw [fields.2.1];exact Finset.subset_insert _ _)
  exact ⟨by simpa only [comparisonStored_length] using actual,afterHeader⟩
end PDLower.CoreSearch.Located
