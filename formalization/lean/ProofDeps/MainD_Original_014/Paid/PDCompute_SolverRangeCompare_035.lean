module

public import Paid.PDCompute_SolverEndpointHeader_034

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)
open PDMenu.ComputeFrame

def rangeCompareCode : List Instruction :=
  loadSlot 25 .index++loadSlot 6 .value++[.natCompare .lessEqual .flag .index .value]

def rangeCompareResult (before : State) (base index last : ℕ) : State :=
  let loaded := loadSlotResult (loadSlotResult before base 25 .index) base 6 .value
  ({loaded with pc:=loaded.pc+1}).set .flag (.natural (if index ≤ last then 1 else 0))

theorem rangeCompareCode_length : rangeCompareCode.length=7 := rfl

theorem rangeCompareCode_straight : StraightCode rangeCompareCode := by
  intro instruction member
  simp only [rangeCompareCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|(h|h|h))|h <;> subst instruction <;> trivial

theorem rangeCompareCode_execute (input : List Cell) (before : State) (base : ℕ) (values : ℕ → Cell)
    (index last : ℕ) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hi : values 25=.natural index) (hl : values 6=.natural last) :
    linearExecute input rangeCompareCode before=some (rangeCompareResult before base index last) := by
  have hil := header.live 25 (by decide)
  have hll := header.live 6 (by decide)
  have hiv := (header.value 25 (by decide)).trans hi
  have hlv := (header.value 6 (by decide)).trans hl
  simp [rangeCompareCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    hbase,hil,hll,hiv,hlv,Comparison.nat,rangeCompareResult,loadSlotResult]

theorem rangeCompareResult_fields (before : State) (base index last : ℕ) :
    (rangeCompareResult before base index last).heap=before.heap ∧
    (rangeCompareResult before base index last).live=before.live ∧
    (rangeCompareResult before base index last).register .fresh=before.register .fresh ∧
    (rangeCompareResult before base index last).register .flag=.natural (if index ≤ last then 1 else 0) ∧
    (rangeCompareResult before base index last).pc=before.pc+7 ∧
    (rangeCompareResult before base index last).output=before.output := by
  simp [rangeCompareResult,loadSlotResult,State.set]

end PDCompute.Solver
