module

public import Paid.PDLower_CalibrationCompute_Constants_021
public import Paid.RootD27Bits_SlotPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Bits

namespace PDLower.CalibrationCompute

/-- All four literal constantSlot prefixes keep the SAME real caller
budget. Untouched registers/output/heap remain covered by caller SafeBits;
only the actually assigned Cell and address/PC arithmetic need bounds. -/
theorem constantSlot_prefix_safe (input : List Cell) (before after : State)
    (base offset budget count : ℕ) (value : Cell)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (valueBits : value.bits≤budget) (addressBits : 1+natBits (base+offset)≤budget)
    (pcBits : natBits (before.pc+4)≤budget) (bound : count≤4)
    (executed : linearExecute input ((constantSlot offset value).take count) before=some after) :
    SafeBits after budget := by
  cases count with
  | zero =>
    have same : before=after := Option.some.inj executed
    subst after
    exact safe
  | succ count =>
    let first : State := ({before with pc:=before.pc+1}).set .value value
    change linearExecute input ((storeSlot offset .value).take count) first=some after at executed
    have earlyPC : natBits (before.pc+1)≤budget :=
      (PDROC.DataBits.natBits_mono (by omega : before.pc+1≤before.pc+4)).trans pcBits
    have firstSafe : SafeBits first budget :=
      (safe.withPC (before.pc+1) earlyPC).set .value value valueBits
    have firstFresh : first.register .fresh=.natural base := by
      simpa only [first,State.set,Function.update_of_ne (by decide : (.fresh : Register)≠.value)] using fresh
    have firstPC : natBits (first.pc+3)≤budget := by
      simpa only [first,State.set,Nat.add_assoc] using pcBits
    exact RootD27.Bits.storeSlot_prefix_safe input first after base offset budget count .value
      firstSafe firstFresh (by decide) addressBits firstPC (by omega) executed

end PDLower.CalibrationCompute
