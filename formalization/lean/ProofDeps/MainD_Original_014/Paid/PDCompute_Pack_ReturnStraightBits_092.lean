module
public import Paid.PDCompute_Pack_BitBudget_057
public import Paid.PDCompute_Pack_SlotBitTrace_064
public import Paid.PDCompute_Pack_SmallBits_060
public import Paid.PDCompute_Pack_Return_043

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)

theorem returnStraight_prefix_safe (input : List Cell) (before after : State) (base returnPC start cursor budget count : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (_hreturn : values 1=.natural returnPC) (hstart : values outputStart=.natural start) (hcursor : values outputCursor=.natural cursor)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (counter : natBits (before.pc+10) ≤ budget) (bound : count ≤ 10)
    (execute : linearExecute input (returnStraightCode.take count) before=some after) : SafeBits after budget := by
  let first:=loadSlotResult before base 1 .old
  let second:=loadSlotResult first base outputCursor .index
  let third:=loadSlotResult second base outputStart .address
  have head1 : Header first base values:=header
  have head2 : Header second base values:=header
  have base1 : first.register .fresh=.natural base:=(loadSlotResult_fresh before base 1 .old (by decide)).trans fresh
  have base2 : second.register .fresh=.natural base:=(loadSlotResult_fresh first base outputCursor .index (by decide)).trans base1
  have pc1 : natBits (before.pc+3) ≤ budget:=(natBits_mono (by omega : before.pc+3 ≤ before.pc+10)).trans counter
  have pc2 : natBits (first.pc+3) ≤ budget:=by
    change natBits (before.pc+3+3) ≤ budget
    exact (natBits_mono (by omega : before.pc+3+3 ≤ before.pc+10)).trans counter
  have pc3 : natBits (second.pc+3) ≤ budget:=by
    change natBits (before.pc+3+3+3) ≤ budget
    exact (natBits_mono (by omega : before.pc+3+3+3 ≤ before.pc+10)).trans counter
  have pc4 : natBits (third.pc+1) ≤ budget:=by
    change natBits (before.pc+3+3+3+1) ≤ budget
    simpa only [Nat.add_assoc] using counter
  have safe1 : SafeBits first budget:=loadSlotResult_safe before base 1 budget .old safe (header.live 1 (by decide)) (addressBits 1 (by decide)) pc1
  have safe2 : SafeBits second budget:=loadSlotResult_safe first base outputCursor budget .index safe1 (head1.live outputCursor (by decide))
    (addressBits outputCursor (by decide)) pc2
  have safe3 : SafeBits third budget:=loadSlotResult_safe second base outputStart budget .address safe2 (head2.live outputStart (by decide))
    (addressBits outputStart (by decide)) pc3
  have index2 : second.register .index=.natural cursor:=(head1.loadSlot_execute input outputCursor .index (by decide) base1).2.trans hcursor
  have index3 : third.register .index=.natural cursor:=by simpa [third,loadSlotResult] using index2
  have address3 : third.register .address=.natural start:=(head2.loadSlot_execute input outputStart .address (by decide) base2).2.trans hstart
  have cursorBits:=header_values_safe safe header outputCursor (by decide)
  rw [hcursor] at cursorBits
  have resultBits : 1+natBits (cursor-start) ≤ budget:=by
    change 1+natBits cursor ≤ budget at cursorBits
    exact (Nat.add_le_add_left (natBits_mono (Nat.sub_le cursor start)) 1).trans cursorBits
  have run1:=(header.loadSlot_execute input 1 .old (by decide) fresh).1
  have run2:=(head1.loadSlot_execute input outputCursor .index (by decide) base1).1
  have run3:=(head2.loadSlot_execute input outputStart .address (by decide) base2).1
  have prefix1 : ∀ take ≤ (loadSlot 1 .old).length,∀ state,
      linearExecute input ((loadSlot 1 .old).take take) before=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact loadSlot_prefix_safe input before state base 1 budget take .old safe fresh (header.live 1 (by decide)) (addressBits 1 (by decide)) pc1 takeBound run
  have prefix2 : ∀ take ≤ (loadSlot outputCursor .index).length,∀ state,
      linearExecute input ((loadSlot outputCursor .index).take take) first=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact loadSlot_prefix_safe input first state base outputCursor budget take .index safe1 base1 (head1.live outputCursor (by decide))
      (addressBits outputCursor (by decide)) pc2 takeBound run
  have prefix3 : ∀ take ≤ (loadSlot outputStart .address).length,∀ state,
      linearExecute input ((loadSlot outputStart .address).take take) second=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact loadSlot_prefix_safe input second state base outputStart budget take .address safe2 base2 (head2.live outputStart (by decide))
      (addressBits outputStart (by decide)) pc3 takeBound run
  have prefix4:=instruction_prefix_invariant input (.natOp .subtract .index .index .address) third (fun state=>SafeBits state budget) safe3
    (fun state run=>natOp_execute_safe input third state .subtract .index .index .address cursor start (cursor-start) budget
      safe3 index3 address3 rfl resultBits pc4 run)
  have tail:=invariant_prefix_append input (loadSlot outputStart .address) [.natOp .subtract .index .index .address] second third run3
    (fun state=>SafeBits state budget) prefix3 prefix4
  have middle:=invariant_prefix_append input (loadSlot outputCursor .index) (loadSlot outputStart .address++[.natOp .subtract .index .index .address])
    first second run2 (fun state=>SafeBits state budget) prefix2 tail
  have combined:=invariant_prefix_append input (loadSlot 1 .old)
    (loadSlot outputCursor .index++(loadSlot outputStart .address++[.natOp .subtract .index .index .address])) before first run1
    (fun state=>SafeBits state budget) prefix1 middle
  have allPrefixes : ∀ take ≤ returnStraightCode.length,∀ state,
      linearExecute input (returnStraightCode.take take) before=some state → SafeBits state budget:=by
    simpa only [returnStraightCode,List.append_assoc] using combined
  exact allPrefixes count bound after execute

end PDCompute.Pack
