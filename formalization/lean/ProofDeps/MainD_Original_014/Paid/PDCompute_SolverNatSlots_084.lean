module

public import Paid.PDCompute_SolverMemoryJoin_062
public import Paid.PDROC_D27Prepare_Program_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot)
open PDMenu.ComputeFrame

/-- This notation expands to ten original typed ISA instructions, for
actual row/column/address arithmetic; it is not a machine primitive. -/
def natBinarySlots (operation : NatOp) (left right target : ℕ) : List Instruction :=
  PDROC.D27Prepare.Program.natBinarySlots operation left right target

def natBinarySlotsResult (before : State) (base left right target _x _y value : ℕ) : State :=
  PDROC.D27Prepare.Program.natBinarySlotsResult before base left right target value

theorem natBinarySlots_length (operation : NatOp) (left right target : ℕ) :
    (natBinarySlots operation left right target).length=10 := rfl

theorem natBinarySlots_straight (operation : NatOp) (left right target : ℕ) :
    StraightCode (natBinarySlots operation left right target) :=
  PDROC.D27Prepare.Program.natBinarySlots_straight operation left right target

theorem natBinarySlots_execute (input : List Cell) (before : State) (base left right target x y value : ℕ)
    (operation : NatOp) (values : ℕ → Cell) (header : Header before base values)
    (hl : left < headerWords) (hr : right < headerWords)
    (hx : values left=.natural x) (hy : values right=.natural y)
    (hbase : before.register .fresh=.natural base) (hoperation : operation.eval x y=some value) :
    linearExecute input (natBinarySlots operation left right target) before=
      some (natBinarySlotsResult before base left right target x y value) := by
  exact PDROC.D27Prepare.Program.natBinarySlots_execute input before base left right target operation x y value hbase
    (header.live left hl) (header.live right hr) ((header.value left hl).trans hx) ((header.value right hr).trans hy) hoperation

theorem natBinarySlots_header (before : State) (base left right target x y value : ℕ) (values : ℕ → Cell)
    (header : Header before base values) :
    Header (natBinarySlotsResult before base left right target x y value) base
      (Function.update values target (.natural value)) := by
  have fields:=PDROC.D27Prepare.Program.natBinarySlotsResult_fields before base left right target value
  apply Header.update header target (.natural value) fields.1
  rw [fields.2.1]
  exact Finset.subset_insert _ _

theorem natBinarySlots_prefix_memory (input : List Cell) (before after : State)
    (base left right target x y value : ℕ) (operation : NatOp) (values : ℕ → Cell)
    (header : Header before base values) (hl : left < headerWords) (hr : right < headerWords)
    (ht : target < headerWords) (hx : values left=.natural x) (hy : values right=.natural y)
    (hbase : before.register .fresh=.natural base) (hoperation : operation.eval x y=some value)
    (count : ℕ) (bound : count ≤ 10)
    (execute : linearExecute input ((natBinarySlots operation left right target).take count) before=some after) :
    HeaderMemory before after base := by
  have leftLive:=header.live left hl
  have rightLive:=header.live right hr
  have leftCell:=(header.value left hl).trans hx
  have rightCell:=(header.value right hr).trans hy
  simp only [NatOp.eval] at hoperation
  interval_cases count <;>
    simp [natBinarySlots,PDROC.D27Prepare.Program.natBinarySlots,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      hbase,leftLive,rightLive,leftCell,rightCell,hoperation] at execute <;> subst after
  all_goals first
    | exact HeaderMemory.of_unchanged base rfl rfl rfl
    | exact HeaderMemory.write header target ht (.natural value) rfl rfl rfl

theorem natBinarySlots_trace_memory (program : Program) (input : List Cell) (before : State)
    (base left right target x y value n k : ℕ) (operation : NatOp) (values : ℕ → Cell)
    (header : Header before base values) (hl : left < headerWords) (hr : right < headerWords)
    (ht : target < headerWords) (hx : values left=.natural x) (hy : values right=.natural y)
    (hbase : before.register .fresh=.natural base) (hoperation : operation.eval x y=some value)
    (fetch : FetchesCode program before.pc (natBinarySlots operation left right target)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (natBinarySlotsResult before base left right target x y value) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 165 ∧
      Header (natBinarySlotsResult before base left right target x y value) base (Function.update values target (.natural value)) ∧
      Frame before (natBinarySlotsResult before base left right target x y value) base n k ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  obtain ⟨trace,hh,hlast,hchain,htime,memory⟩ :=
    linearExecute_trace_memory program input (natBinarySlots operation left right target)
      (natBinarySlots_straight operation left right target) before _ base fetch
      (natBinarySlots_execute input before base left right target x y value operation values header hl hr hx hy hbase hoperation)
      (fun count bound state execute => natBinarySlots_prefix_memory input before state base left right target x y value operation values
        header hl hr ht hx hy hbase hoperation count bound execute)
  have fields:=PDROC.D27Prepare.Program.natBinarySlotsResult_fields before base left right target value
  exact ⟨trace,hh,hlast,hchain,htime,natBinarySlots_header before base left right target x y value values header,
    slotWrite_frame before _ base target n k (.natural value) ht fields.1 fields.2.1,memory⟩

end PDCompute.Solver
