module

public import Paid.RootD27Bits_Update_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Bits

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute)

def addressCode (slot : ℕ) : List Instruction :=
  [.constant .address (.natural slot),.natOp .add .address .fresh .address]

def addressOne (before : State) (slot : ℕ) : State :=
  ({before with pc:=before.pc+1}).set .address (.natural slot)

def addressTwo (before : State) (base slot : ℕ) : State :=
  ({addressOne before slot with pc:=before.pc+2}).set .address (.natural (base+slot))

theorem addressOne_safe (before : State) (base slot budget : ℕ) (safe : SafeBits before budget)
    (addressBits : 1+natBits (base+slot)≤budget) (pcBits : natBits (before.pc+3)≤budget) :
    SafeBits (addressOne before slot) budget := by
  have slotBits : (.natural slot : Cell).bits≤budget := by
    have mono:=natBits_mono (by omega : slot≤base+slot)
    change 1+natBits slot≤budget
    omega
  have counter:= (natBits_mono (by omega : before.pc+1≤before.pc+3)).trans pcBits
  exact (safe.withPC (before.pc+1) counter).set .address (.natural slot) slotBits

theorem addressTwo_safe (before : State) (base slot budget : ℕ) (safe : SafeBits before budget)
    (addressBits : 1+natBits (base+slot)≤budget) (pcBits : natBits (before.pc+3)≤budget) :
    SafeBits (addressTwo before base slot) budget := by
  have first:=addressOne_safe before base slot budget safe addressBits pcBits
  have counter:=(natBits_mono (by omega : before.pc+2≤before.pc+3)).trans pcBits
  exact (first.withPC (before.pc+2) counter).set .address (.natural (base+slot)) addressBits

/-- Both real address-construction instructions, with any unexecuted
third instruction. The same fixed budget covers every successful prefix. -/
theorem address_prefix_safe (input : List Cell) (before after : State) (base slot budget count : ℕ)
    (last : Instruction) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base)
    (addressBits : 1+natBits (base+slot)≤budget) (pcBits : natBits (before.pc+3)≤budget)
    (bound : count≤2)
    (executed : linearExecute input ((addressCode slot++[last]).take count) before=some after) :
    SafeBits after budget := by
  interval_cases count <;>
    simp [addressCode,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,fresh,Nat.add_assoc] at executed
  · subst after
    exact safe
  · subst after
    exact addressOne_safe before base slot budget safe addressBits pcBits
  · subst after
    exact addressTwo_safe before base slot budget safe addressBits pcBits

end RootD27.Bits
