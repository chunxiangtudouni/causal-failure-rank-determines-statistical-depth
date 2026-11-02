module

public import Paid.PDROC_CalibrationRow_ControlOperands_001
public import Paid.PDLower_CalibrationCompute_ConstantBits_082

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- Only adapts the proved original082 macro to PrefixSafe. No opcode
or four-instruction execution proof is duplicated here. -/
theorem constantSlot_sameBudget (input : List Cell) (before : State) (base offset budget : ℕ) (value : Cell)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (valueBits : value.bits≤budget) (addressBits : 1+natBits (base+offset)≤budget)
    (pcBits : natBits (before.pc+4)≤budget) :
    PrefixSafe input (constantSlot offset value) before budget := by
  apply PrefixSafe.of_bounded
  intro count bound after run
  exact PDLower.CalibrationCompute.constantSlot_prefix_safe input before after base offset budget count value
    safe fresh valueBits addressBits pcBits (by change count≤4 at bound; exact bound) run

/-- The same proof handles reset6 and reset7. In reset6, incoming heap6
may still be an arbitrary caller Cell; its bound is carried until the
REAL constantSlot store creates Nat0. -/
theorem reset_body_prefix_safe (input : List Cell) (P : Parameters) (origin base budget offset : ℕ)
    (label : Label) (before : State) (bounds : ControlBudget P origin base budget)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (position : before.pc=labelAddress origin label) (offsetBound : offset≤16)
    (code : (basicBlock label).body=constantSlot offset (.natural 0)) :
    PrefixSafe input (basicBlock label).body before budget := by
  rw [code]
  exact constantSlot_sameBudget input before base offset budget (.natural 0) safe fresh
    (ControlBudget.literal P origin base budget 0 bounds (by decide))
    (ControlBudget.slot P origin base budget offset bounds offsetBound)
    (ControlBudget.pc_prefix P origin base budget bounds before label 4 position (by decide))

end PDROC.CalibrationRow.Operand
