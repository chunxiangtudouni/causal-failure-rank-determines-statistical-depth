module

public import Paid.PDROC_BitVM_VM_Phases_Program_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.VM.Phases

open Turing PaperProofs.Paid.Computation

/-- Original bits are on physical stack0 and every other stack is
actually empty at the TM2 initial configuration. The raw Bool bootstrap
produces this exact encoded configuration, before the first real mount. -/
def rawContents (bits : List Bool) : ISA.Stack → List Bool :=
  Function.update (fun _ => []) 0 bits

theorem before_eq_init (backend : ISA.RatBackend) (prepareCode coreCode : Program) (bits : List Bool) :
    before backend prepareCode coreCode (rawContents bits) =
      (TM2.init (0 : ISA.Stack) bits : State backend prepareCode coreCode) := rfl

theorem rawContents_zero (bits : List Bool) : rawContents bits 0 = bits := by
  simp only [rawContents, Function.update_self]

theorem rawContents_other (bits : List Bool) (role : ISA.Stack) (different : role ≠ 0) :
    rawContents bits role = [] := Function.update_of_ne different _ _

/-- The final TRUE footer is part of the original official codec.
It discharges the physical output decoder's nonempty condition; it is
not a supplied output bit or a new machine/input qualification. -/
theorem encoded_nonempty (cells : List Cell) : encodeBits cells ≠ [] := by
  simp [encodeBits]

end PDROC.BitVM.VM.Phases
