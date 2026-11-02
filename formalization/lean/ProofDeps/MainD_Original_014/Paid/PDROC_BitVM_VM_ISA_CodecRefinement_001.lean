module

public import Paid.PDROC_BitVM_VM_ISA_Specification_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.CodecRefinement

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-- This is only projection of the exact OLD macro endpoint frame.
The four real typed-register codecs change no heap event or output.
No cleanup, workspace bound or new execution witness is supplied. -/
theorem register_observables (input : List Cell)
    (logical next : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent)
    (contents final : Stack → List Bool) (target : Register)
    (ready : Source.Observables input logical events contents)
    (registers : ∀ reg, final (registerSlot reg) = encodeCellBits (next.register reg))
    (heap : next.heap = logical.heap) (live : next.live = logical.live) (output : next.output = logical.output)
    (frame : ∀ role, role ≠ 0 → role ≠ 24 → role ≠ 25 → role ≠ 26 →
      role ≠ registerSlot target → final role = contents role) :
    Source.Observables input next events final := by
  apply Source.observables_register_step input logical next events contents final ready registers heap live output
  · intro field
    exact frame (Log.BankDrain.bankSlot field)
      (Log.BankDrain.bankSlot_ne field 0 (by decide))
      (Log.BankDrain.bankSlot_ne field 24 (by decide))
      (Log.BankDrain.bankSlot_ne field 25 (by decide))
      (Log.BankDrain.bankSlot_ne field 26 (by decide))
      (Log.BankDrain.bankSlot_ne field (registerSlot target) (Or.inr (registerSlot_bounds target).1))
  · exact frame 21 (by decide) (by decide) (by decide) (by decide) (by cases target <;> decide)
  · exact frame 22 (by decide) (by decide) (by decide) (by decide) (by cases target <;> decide)
  · exact frame 23 (by decide) (by decide) (by decide) (by decide) (by cases target <;> decide)

end PDROC.BitVM.VM.ISA.CodecRefinement
