module

public import Paid.PDROC_BitVM_VM_ISA_Specification_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.VM.ISA

open PaperProofs.Paid.Computation

def Protected (role : Stack) : Prop :=
  (1 ≤ role.val ∧ role.val ≤ 13) ∨ (21 ≤ role.val ∧ role.val ≤ 23)

theorem protected_bounds (role : Stack) (safe : Protected role) : 1 ≤ role.val ∧ role.val < 24 := by
  rcases safe with bank | event <;> omega

theorem protected_not_register (role : Stack) (safe : Protected role) (reg : Register) :
    role ≠ Kernel.RegisterGlobal.registerSlot reg := by
  have bounds := Kernel.RegisterGlobal.registerSlot_bounds reg
  intro same
  have values := congrArg Fin.val same
  rcases safe with bank | event <;> omega

theorem protected_not_zero (role : Stack) (safe : Protected role) : role ≠ 0 := by
  have bounds := protected_bounds role safe
  intro same
  subst role
  omega

theorem protected_not_work (role work : Stack) (safe : Protected role) (large : 24 ≤ work.val) : role ≠ work := by
  have bounds := protected_bounds role safe
  intro same
  have values := congrArg Fin.val same
  omega

/-- One common observable frame for all arithmetic/register opcodes.
Original registers are supplied by their existing semantic theorem;
readonly bank, heap event tape and output tapes are strictly carried. -/
theorem observables_register_from_frame (input : List Cell)
    (logical next : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent)
    (before after : Stack → List Bool) (represented : Source.Observables input logical events before)
    (registers : ∀ reg, after (Kernel.RegisterGlobal.registerSlot reg) = encodeCellBits (next.register reg))
    (heap : next.heap = logical.heap) (live : next.live = logical.live) (output : next.output = logical.output)
    (frame : ∀ role, Protected role → after role = before role) :
    Source.Observables input next events after := by
  apply Source.observables_register_step input logical next events before after represented registers heap live output
  · intro field
    apply frame
    left
    change 1 ≤ field.val+1 ∧ field.val+1 ≤ 13
    omega
  · exact frame 21 (Or.inr (by decide))
  · exact frame 22 (Or.inr (by decide))
  · exact frame 23 (Or.inr (by decide))

end PDROC.BitVM.VM.ISA
