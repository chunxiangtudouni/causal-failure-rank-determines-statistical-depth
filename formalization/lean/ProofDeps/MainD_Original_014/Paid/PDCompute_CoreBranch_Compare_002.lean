module
public import Paid.PDCompute_CoreBranch_Data_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
@[expose] public section
namespace PDCompute.CoreBranch
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

/-- Actual one/two comparison prefixes. Physical midpoint data survives
their precise40 final frame; all resources use the stored real chain. -/
structure Prefix (program : Program) (input : List Cell) (P : Parameters) (fee penalty : ℚ)
    (lower upper : MultiplierSolve) (budget origin : ℕ) (before after : State) (cost : ℕ) where
  trace : List State
  head : trace.head?=some before
  last : trace.getLast?=some after
  chain : trace.IsChain (fun first later=>step program input first=some later)
  timeBound : time program trace≤cost
  ready : Ready P fee after
  represented : SearchStateRep P fee after (.bracket lower upper)
  data : MidpointData P fee penalty after
  frame : RegionMemory before after {40}
  properties : ∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget
  scope : ∀ state∈trace,origin+251≤state.pc ∧ state.pc≤origin+515
  space : peakCells trace≤workingCells before

def Prefix.join {program : Program} {input : List Cell} {P : Parameters} {fee penalty : ℚ}
    {lower upper : MultiplierSolve} {budget origin : ℕ} {before middle after : State} {c d : ℕ}
    (first : Prefix program input P fee penalty lower upper budget origin before middle c)
    (later : Prefix program input P fee penalty lower upper budget origin middle after d) :
    Prefix program input P fee penalty lower upper budget origin before after (c+d) := by
  have joined:=joinTrace_spec program input first.trace later.trace before middle after c d
    first.head first.last later.head later.last first.chain later.chain first.timeBound later.timeBound
  have memory:=RegionMemory.join_trace first.trace later.trace before middle scalarRegion first.last
    (fun state member=>(first.properties state member).1) (fun state member=>(later.properties state member).1)
  have bits:=PDCompute.Pack.joinTrace_invariant first.trace later.trace
    (fun state=>RootD27.Bits.SafeBits state budget)
    (fun state member=>(first.properties state member).2) (fun state member=>(later.properties state member).2)
  have middleSpace:=(workingCells_le_peak_of_member first.trace middle (List.mem_of_getLast? first.last)).trans first.space
  have allSpace : ∀ state∈joinTrace first.trace later.trace,workingCells state≤workingCells before := by
    intro state member
    rcases joinTrace_member member with early|late
    · exact (workingCells_le_peak_of_member first.trace state early).trans first.space
    · exact ((workingCells_le_peak_of_member later.trace state late).trans later.space).trans middleSpace
  exact ⟨joinTrace first.trace later.trace,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    later.ready,later.represented,later.data,first.frame.trans later.frame,
    (fun state member=>⟨memory state member,bits state member⟩),
    PDCompute.Pack.joinTrace_invariant first.trace later.trace _ first.scope later.scope,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace⟩

theorem comparison_prefix (P : Parameters) (fee penalty : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (comparison : Comparison) (left right : ℕ) (x y : ℚ) (zeroPC onePC budget origin : ℕ)
    (ready : Ready P fee before) (represented : SearchStateRep P fee before (.bracket lower upper))
    (data : MidpointData P fee penalty before) (safe : RootD27.Bits.SafeBits before budget)
    (small : 7≤budget) (endBits : (Cell.natural (origin+516)).bits≤budget)
    (belowEntry : origin+516<labels.solveEntry)
    (position : origin+251≤before.pc ∧ before.pc+11≤origin+516)
    (zeroBound : origin+251≤zeroPC ∧ zeroPC≤origin+515)
    (oneBound : origin+251≤onePC ∧ onePC≤origin+515)
    (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : before.heap left=.rational x) (rightValue : before.heap right=.rational y)
    (fetched : FetchesCode program before.pc (comparisonDecisionCode comparison left right zeroPC onePC)) :
    ∃ after,∃ _prefix : Prefix program input P fee penalty lower upper budget origin before after 180,
      after.pc=comparisonDecisionTarget comparison x y zeroPC onePC := by
  have endNat : natBits (origin+516)≤budget := by change 1+natBits (origin+516)≤budget at endBits;omega
  have addressBits : 1+natBits headerWords≤budget := (show 1+natBits headerWords≤7 by decide).trans small
  obtain ⟨trace,after,head,last,chain,cost,pc,fresh,header,rep,precise,properties,scope,_proper,
    space,_requests,_count,_refinement⟩:=
    represented_comparison_decision_actual P fee (.bracket lower upper) comparison left right x y
      program labels input before zeroPC onePC budget 40000 ready.header ready.fresh represented leftInside rightInside
      leftValue rightValue safe (by omega) addressBits
      ((PDROC.DataBits.natBits_mono position.2).trans endNat)
      ((PDROC.DataBits.natBits_mono (by omega : zeroPC≤origin+516)).trans endNat)
      ((PDROC.DataBits.natBits_mono (by omega : onePC≤origin+516)).trans endNat)
      (by omega) (by omega) (by omega) fetched
  have targetBounds : origin+251≤comparisonDecisionTarget comparison x y zeroPC onePC ∧
      comparisonDecisionTarget comparison x y zeroPC onePC≤origin+515 := by
    unfold comparisonDecisionTarget
    split_ifs <;> assumption
  have locations : ∀ state∈trace,origin+251≤state.pc ∧ state.pc≤origin+515 := by
    intro state member
    rcases scope state member with inline|terminal <;> omega
  let result : Prefix program input P fee penalty lower upper budget origin before after 180:=
    ⟨trace,head,last,chain,cost,ready_after_comparison ready header fresh precise,rep,data.preserve precise,
      precise,properties,locations,space⟩
  exact ⟨after,result,pc⟩

end PDCompute.CoreBranch
