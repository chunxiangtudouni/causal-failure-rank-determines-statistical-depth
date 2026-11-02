module

public import Paid.PDCompute_SolverPrefixResources_134
public import Paid.PDCompute_SolverPaddingPairFields_135
public import Paid.PDCompute_SolverBaseRowStep_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute)

theorem baseRowWrites_pairs : baseRowWrites=
    [.constant .value (.natural 0)]++paddingPairsCode 3++[.constant .value (.rational 0)]++paddingPairsCode 3++paddingDecrementCode := rfl

/-- EVERY prefix of the SAME original15-op padding body, with the
genuine natural/rational zero fields, six real stores and real decrement.
No preinitialized Header or oldlive-disjointness premise is used. -/
theorem baseRowWrites_prefix_resources (input : List Cell) (before after : State) (base pointer index budget count : ℕ)
    (address : before.register .address=.natural pointer) (current : before.register .index=.natural index)
    (one : before.register .flag=.natural 1) (safe : RootD27.Bits.SafeBits before budget)
    (lower : base ≤ pointer) (room : pointer+6 ≤ base+headerWords)
    (addressBits : 1+natBits (base+headerWords) ≤ budget) (zeroBits : (.rational 0 : Cell).bits ≤ budget)
    (pcBits : natBits (before.pc+15) ≤ budget) (countBound : count ≤ baseRowWrites.length)
    (executed : linearExecute input (baseRowWrites.take count) before=some after) :
    RegionMemory before after (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits after budget := by
  let region:=cellRegion base headerWords
  let naturalStart:=paddingConstantResult before .value (.natural 0)
  have pcWithin (counter : ℕ) (bound : counter ≤ before.pc+15) : natBits counter ≤ budget := (natBits_mono bound).trans pcBits
  have naturalZeroBits : (.natural 0 : Cell).bits ≤ budget := by
    have mono:=natBits_mono (Nat.zero_le (base+headerWords))
    change 1+natBits 0 ≤ budget
    omega
  have naturalRun : linearExecute input [.constant .value (.natural 0)] before=some naturalStart := rfl
  have naturalResources : CodePrefixResources input [.constant .value (.natural 0)] before region budget := by
    intro prefixCount bound state run
    exact paddingConstant_prefix_resources input before state budget prefixCount .value (.natural 0) safe naturalZeroBits
      (pcWithin _ (by omega)) bound run region
  have naturalSafe:=(naturalResources.full naturalRun).2
  have addressDifferent : (.address : Register) ≠ .value := by decide
  have flagDifferent : (.flag : Register) ≠ .value := by decide
  have indexDifferent : (.index : Register) ≠ .value := by decide
  have naturalAddress : naturalStart.register .address=.natural pointer := by
    simpa only [naturalStart,paddingConstantResult,State.set,Function.update_of_ne addressDifferent] using address
  have naturalOne : naturalStart.register .flag=.natural 1 := by
    simpa only [naturalStart,paddingConstantResult,State.set,Function.update_of_ne flagDifferent] using one
  have naturalIndex : naturalStart.register .index=.natural index := by
    simpa only [naturalStart,paddingConstantResult,State.set,Function.update_of_ne indexDifferent] using current
  have firstPC : natBits (naturalStart.pc+6) ≤ budget := pcWithin _ (by change before.pc+1+6 ≤ before.pc+15; omega)
  have firstResources : CodePrefixResources input (paddingPairsCode 3) naturalStart region budget := by
    intro prefixCount bound state run
    exact paddingPairs_prefix_resources 3 input naturalStart state base pointer budget prefixCount naturalSafe naturalAddress naturalOne lower
      (by omega) addressBits firstPC (by simpa only [paddingPairsCode_length] using bound) run
  obtain ⟨naturalEnd,firstRun,firstAddress,firstOne,firstPreserve,firstCounter⟩:=
    paddingPairs_execute_fields 3 input naturalStart pointer naturalAddress naturalOne
  have firstSafe:=(firstResources.full firstRun).2
  have firstIndex : naturalEnd.register .index=.natural index := (firstPreserve .index (by decide)).trans naturalIndex
  let rationalStart:=paddingConstantResult naturalEnd .value (.rational 0)
  have rationalRun : linearExecute input [.constant .value (.rational 0)] naturalEnd=some rationalStart := rfl
  have rationalPC : natBits (naturalEnd.pc+1) ≤ budget := pcWithin _ (by rw [firstCounter]; change before.pc+1+6+1 ≤ before.pc+15; omega)
  have rationalResources : CodePrefixResources input [.constant .value (.rational 0)] naturalEnd region budget := by
    intro prefixCount bound state run
    exact paddingConstant_prefix_resources input naturalEnd state budget prefixCount .value (.rational 0) firstSafe zeroBits rationalPC bound run region
  have rationalSafe:=(rationalResources.full rationalRun).2
  have rationalAddress : rationalStart.register .address=.natural (pointer+3) := by
    simpa only [rationalStart,paddingConstantResult,State.set,Function.update_of_ne addressDifferent] using firstAddress
  have rationalOne : rationalStart.register .flag=.natural 1 := by
    simpa only [rationalStart,paddingConstantResult,State.set,Function.update_of_ne flagDifferent] using firstOne
  have rationalIndex : rationalStart.register .index=.natural index := by
    simpa only [rationalStart,paddingConstantResult,State.set,Function.update_of_ne indexDifferent] using firstIndex
  have secondPC : natBits (rationalStart.pc+6) ≤ budget := pcWithin _ (by
    change naturalEnd.pc+1+6 ≤ before.pc+15
    rw [firstCounter]
    change before.pc+1+6+1+6 ≤ before.pc+15
    omega)
  have secondResources : CodePrefixResources input (paddingPairsCode 3) rationalStart region budget := by
    intro prefixCount bound state run
    exact paddingPairs_prefix_resources 3 input rationalStart state base (pointer+3) budget prefixCount rationalSafe rationalAddress rationalOne
      (by omega) (by omega) addressBits secondPC (by simpa only [paddingPairsCode_length] using bound) run
  obtain ⟨rationalEnd,secondRun,_,secondOne,secondPreserve,secondCounter⟩:=
    paddingPairs_execute_fields 3 input rationalStart (pointer+3) rationalAddress rationalOne
  have secondSafe:=(secondResources.full secondRun).2
  have secondIndex : rationalEnd.register .index=.natural index := (secondPreserve .index (by decide)).trans rationalIndex
  have decrementPC : natBits (rationalEnd.pc+1) ≤ budget := pcWithin _ (by
    rw [secondCounter]
    change naturalEnd.pc+1+6+1 ≤ before.pc+15
    rw [firstCounter]
    change before.pc+1+6+1+6+1 ≤ before.pc+15
    omega)
  have decrementResources : CodePrefixResources input paddingDecrementCode rationalEnd region budget := by
    intro prefixCount bound state run
    exact paddingDecrement_prefix_resources input rationalEnd state index budget prefixCount secondIndex secondOne secondSafe decrementPC bound run region
  have firstWholeRun : linearExecute input ([.constant .value (.natural 0)]++paddingPairsCode 3) before=some naturalEnd := by
    rw [PDLower.CalibrationCompute.linearExecute_append,naturalRun,Option.bind_some]
    exact firstRun
  have middleWholeRun : linearExecute input ([.constant .value (.natural 0)]++paddingPairsCode 3++[.constant .value (.rational 0)]) before=some rationalStart := by
    rw [PDLower.CalibrationCompute.linearExecute_append,firstWholeRun,Option.bind_some]
    exact rationalRun
  have lastWholeRun : linearExecute input ([.constant .value (.natural 0)]++paddingPairsCode 3++[.constant .value (.rational 0)]++paddingPairsCode 3)
      before=some rationalEnd := by
    rw [PDLower.CalibrationCompute.linearExecute_append,middleWholeRun,Option.bind_some]
    exact secondRun
  have wholeResources:=(((naturalResources.append firstResources naturalRun).append rationalResources firstWholeRun).append
    secondResources middleWholeRun).append decrementResources lastWholeRun
  rw [baseRowWrites_pairs] at executed countBound
  exact wholeResources count countBound after executed

end PDCompute.Solver
