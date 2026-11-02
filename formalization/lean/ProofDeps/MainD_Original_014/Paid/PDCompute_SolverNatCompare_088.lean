module

public import Paid.PDCompute_SolverNatSlots_084

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot)
open PDMenu.ComputeFrame

/-- Reuse the existing frozen arbitrary-base comparison expansion. -/
def naturalCompareCode (comparison : Comparison) (left right : ℕ) : List Instruction :=
  PDROC.D27Prepare.Program.natCompareSlots comparison left right

theorem naturalCompareCode_straight (comparison : Comparison) (left right : ℕ) :
    StraightCode (naturalCompareCode comparison left right) :=
  PDROC.D27Prepare.Program.natCompareSlots_straight comparison left right

theorem naturalCompareCode_prefix_memory (input : List Cell) (before after : State) (base left right x y : ℕ)
    (comparison : Comparison) (values : ℕ → Cell) (header : Header before base values)
    (hl : left < headerWords) (hr : right < headerWords)
    (hx : values left=.natural x) (hy : values right=.natural y)
    (hbase : before.register .fresh=.natural base) (count : ℕ) (bound : count ≤ 7)
    (execute : linearExecute input ((naturalCompareCode comparison left right).take count) before=some after) :
    HeaderMemory before after base := by
  have leftLive:=header.live left hl
  have rightLive:=header.live right hr
  have leftCell:=(header.value left hl).trans hx
  have rightCell:=(header.value right hr).trans hy
  interval_cases count <;>
    simp [naturalCompareCode,PDROC.D27Prepare.Program.natCompareSlots,loadSlot,linearExecute,
      Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,leftLive,rightLive,leftCell,rightCell] at execute <;>
    subst after <;> exact HeaderMemory.of_unchanged base rfl rfl rfl

theorem naturalCompare_trace_memory (program : Program) (input : List Cell) (before : State)
    (base left right x y : ℕ) (comparison : Comparison) (values : ℕ → Cell)
    (header : Header before base values) (hl : left < headerWords) (hr : right < headerWords)
    (hx : values left=.natural x) (hy : values right=.natural y) (hbase : before.register .fresh=.natural base)
    (fetch : FetchesCode program before.pc (naturalCompareCode comparison left right)) :
    ∃ trace : List State,
      trace.head?=some before ∧
      trace.getLast?=some (PDROC.D27Prepare.Program.comparisonResult before base left right (comparison.nat x y)) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 120 ∧ ∀ state ∈ trace, HeaderMemory before state base :=
  linearExecute_trace_memory program input (naturalCompareCode comparison left right)
    (naturalCompareCode_straight comparison left right) before _ base fetch
    (PDROC.D27Prepare.Program.natCompareSlots_execute input before base left right x y comparison hbase
      (header.live left hl) (header.live right hr) ((header.value left hl).trans hx) ((header.value right hr).trans hy))
    (fun count bound state execute =>
      naturalCompareCode_prefix_memory input before state base left right x y comparison values header hl hr hx hy hbase count bound execute)

end PDCompute.Solver
