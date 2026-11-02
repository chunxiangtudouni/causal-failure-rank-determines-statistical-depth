module

public import Paid.PDCompute_SolverScanControl_043

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute linearExecute_append)
open PDMenu.ComputeFrame

def scanAdvanceCode : List Instruction := addNatSlot 25 1++addNatSlot 39 2

def scanAdvanceValues (values : ℕ → Cell) (index pointer : ℕ) : ℕ → Cell :=
  Function.update (Function.update values 25 (.natural (index+1))) 39 (.natural (pointer+2))

theorem addNatSlotResult_frame (before : State) (base slot value amount n k : ℕ)
    (inside : slot < headerWords) : Frame before (addNatSlotResult before base slot value amount) base n k := by
  apply slotWrite_frame before _ base slot n k (.natural (value+amount)) inside
  · exact (addNatSlotResult_fields before base slot value amount).1
  · exact (addNatSlotResult_fields before base slot value amount).2.1

theorem scanAdvanceCode_length : scanAdvanceCode.length=16 := rfl

theorem scanAdvanceCode_straight : StraightCode scanAdvanceCode := by
  intro instruction member
  rcases List.mem_append.mp member with member|member
  · exact addNatSlot_straight 25 1 instruction member
  · exact addNatSlot_straight 39 2 instruction member

theorem scanAdvanceCode_execute (input : List Cell) (before : State) (base n k index pointer : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hi : values 25=.natural index) (hp : values 39=.natural pointer) :
    ∃ after : State, linearExecute input scanAdvanceCode before=some after ∧
      Header after base (scanAdvanceValues values index pointer) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+16 ∧
      Frame before after base n k ∧ after.output=before.output := by
  let first := addNatSlotResult before base 25 index 1
  let after := addNatSlotResult first base 39 pointer 2
  have firstRun := addNatSlot_execute input before base 25 index 1 hbase
    (header.live 25 (by decide)) ((header.value 25 (by decide)).trans hi)
  have firstHeader : Header first base (Function.update values 25 (.natural (index+1))) :=
    header.addNatSlot 25 index 1
  have firstBase : first.register .fresh=.natural base :=
    (addNatSlotResult_fields before base 25 index 1).2.2.1.trans hbase
  have pointerValue : first.heap (base+39)=.natural pointer := by
    have value := firstHeader.value 39 (by decide)
    exact value.trans hp
  have secondRun := addNatSlot_execute input first base 39 pointer 2 firstBase
    (firstHeader.live 39 (by decide)) pointerValue
  refine ⟨after,?_,firstHeader.addNatSlot 39 pointer 2,
    (addNatSlotResult_fields first base 39 pointer 2).2.2.1.trans firstBase,?_,
    (addNatSlotResult_frame before base 25 index 1 n k (by decide)).trans
      (addNatSlotResult_frame first base 39 pointer 2 n k (by decide)),?_⟩
  · rw [scanAdvanceCode,linearExecute_append,firstRun,Option.bind_some]
    exact secondRun
  · change before.pc+8+8=before.pc+16
    omega
  · exact (addNatSlotResult_fields first base 39 pointer 2).2.2.2.2.trans
      (addNatSlotResult_fields before base 25 index 1).2.2.2.2

end PDCompute.Solver
