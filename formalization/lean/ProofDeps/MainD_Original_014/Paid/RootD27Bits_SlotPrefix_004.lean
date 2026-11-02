module

public import Paid.RootD27Bits_AddressPrefix_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Bits

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot loadSlotResult storeSlotResult)

theorem loadSlotResult_safe (before : State) (base slot budget : ℕ) (target : Register)
    (safe : SafeBits before budget) (live : base+slot∈before.live)
    (addressBits : 1+natBits (base+slot)≤budget) (pcBits : natBits (before.pc+3)≤budget) :
    SafeBits (loadSlotResult before base slot target) budget := by
  have addressed:=(safe.withPC (before.pc+3) pcBits).set .address (.natural (base+slot)) addressBits
  have loaded:=addressed.set target (before.heap (base+slot)) (safe.heap (base+slot) live)
  simpa only [loadSlotResult,State.set] using loaded

/-- Original real loadSlot, arbitrary target including.address/.fresh.
Every actual prefix preserves SAME budget and the full original bits. -/
theorem loadSlot_prefix_safe (input : List Cell) (before after : State)
    (base slot budget count : ℕ) (target : Register)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (live : base+slot∈before.live)
    (addressBits : 1+natBits (base+slot)≤budget) (pcBits : natBits (before.pc+3)≤budget)
    (bound : count≤3)
    (executed : linearExecute input ((loadSlot slot target).take count) before=some after) :
    SafeBits after budget := by
  by_cases full : count=3
  · subst count
    change linearExecute input (loadSlot slot target) before=some after at executed
    rw [PDLower.CalibrationCompute.loadSlot_execute input before base slot target fresh live] at executed
    have same:=Option.some.inj executed
    subst after
    exact loadSlotResult_safe before base slot budget target safe live addressBits pcBits
  · exact address_prefix_safe input before after base slot budget count (.load target .address)
      safe fresh addressBits pcBits (by omega) executed

theorem storeSlotResult_safe (before : State) (base slot budget : ℕ) (source : Register)
    (safe : SafeBits before budget)
    (addressBits : 1+natBits (base+slot)≤budget) (pcBits : natBits (before.pc+3)≤budget) :
    SafeBits (storeSlotResult before base slot source) budget := by
  have address : natBits (base+slot)≤budget := by omega
  have written:=safe.store (base+slot) (before.register source) address (safe.register source)
  have addressed:=written.set .address (.natural (base+slot)) addressBits
  have counted:=addressed.withPC (before.pc+3) pcBits
  simpa only [storeSlotResult,State.set] using counted

/-- Original real storeSlot. Existing caller live cells and all original
output/heap/reg bits are covered; no new P-only caller restriction. -/
theorem storeSlot_prefix_safe (input : List Cell) (before after : State)
    (base slot budget count : ℕ) (source : Register)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (different : source≠.address)
    (addressBits : 1+natBits (base+slot)≤budget) (pcBits : natBits (before.pc+3)≤budget)
    (bound : count≤3)
    (executed : linearExecute input ((storeSlot slot source).take count) before=some after) :
    SafeBits after budget := by
  by_cases full : count=3
  · subst count
    change linearExecute input (storeSlot slot source) before=some after at executed
    rw [PDLower.CalibrationCompute.storeSlot_execute input before base slot source fresh different] at executed
    have same:=Option.some.inj executed
    subst after
    exact storeSlotResult_safe before base slot budget source safe addressBits pcBits
  · exact address_prefix_safe input before after base slot budget count (.store .address source)
      safe fresh addressBits pcBits (by omega) executed

end RootD27.Bits
