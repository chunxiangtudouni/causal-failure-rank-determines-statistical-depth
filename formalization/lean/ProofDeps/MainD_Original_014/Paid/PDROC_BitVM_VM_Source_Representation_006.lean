module

public import Paid.PDROC_BitVM_Log_InputLoad_070
public import Paid.PDROC_BitVM_Kernel_Reset_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Source

open PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-- These are proof relations for actual physical tapes, not runtime
RAM states, values, events or output lists in the finite TM store. -/
structure Observables (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool) : Prop where
  registers : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg)
  bank : Log.InputLoad.BankAt input contents
  history : contents 21 = Log.encodeHistory events
  heap : Log.Refines events logical
  outputWord : contents 22 = (logical.output.flatMap encodeCellBits).reverse
  outputTicks : contents 23 = List.replicate logical.output.length true

def WorkspaceEmpty (contents : Stack → List Bool) : Prop :=
  ∀ role, role.val = 0 ∨ 24 ≤ role.val → contents role = []

structure Ready (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool) : Prop
    extends Observables input logical events contents where
  workspace : WorkspaceEmpty contents

/-- A real physical scratch-cleaner supplies frame and empty conclusions.
This lemma only transports the relation; it supplies no free tape change. -/
theorem ready_after_cleanup (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (before after : Stack → List Bool)
    (represented : Observables input logical events before)
    (frame : ∀ role, 1 ≤ role.val ∧ role.val < 24 → after role = before role)
    (empty : WorkspaceEmpty after) : Ready input logical events after := by
  refine ⟨⟨?_,?_,?_,represented.heap,?_,?_⟩,empty⟩
  · intro reg
    have bounds := registerSlot_bounds reg
    exact (frame (registerSlot reg) (by omega)).trans (represented.registers reg)
  · intro field
    have bounds : 1 ≤ (Log.BankDrain.bankSlot field).val ∧ (Log.BankDrain.bankSlot field).val < 24 := by
      change 1 ≤ field.val+1 ∧ field.val+1 < 24
      omega
    exact (frame (Log.BankDrain.bankSlot field) bounds).trans (represented.bank field)
  · exact (frame 21 (by decide)).trans represented.history
  · exact (frame 22 (by decide)).trans represented.outputWord
  · exact (frame 23 (by decide)).trans represented.outputTicks

/-- Data instructions that change only original registers/PC can carry
the same heap history, physical readonly bank and output event tapes. -/
theorem observables_register_step (input : List Cell)
    (logical next : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent)
    (before after : Stack → List Bool) (represented : Observables input logical events before)
    (registers : ∀ reg, after (registerSlot reg) = encodeCellBits (next.register reg))
    (heap : next.heap = logical.heap) (live : next.live = logical.live) (output : next.output = logical.output)
    (bank : ∀ field : Fin 13, after (Log.BankDrain.bankSlot field) = before (Log.BankDrain.bankSlot field))
    (history : after 21 = before 21) (word : after 22 = before 22) (ticks : after 23 = before 23) :
    Observables input next events after := by
  refine ⟨registers,?_,history.trans represented.history,represented.heap.carry heap live,?_,?_⟩
  · intro field
    exact (bank field).trans (represented.bank field)
  · rw [word,represented.outputWord,output]
  · rw [ticks,represented.outputTicks,output]

/-- The actual bank mount and Reset008 provide exactly these premises.
In particular all seven zero registers, history, output and scratch
come from genuine producers rather than a per-instruction assumption. -/
theorem initial_ready (input : List Cell) (contents : Stack → List Bool)
    (registers : ∀ reg, contents (registerSlot reg) = encodeCellBits (initial.register reg))
    (bank : Log.InputLoad.BankAt input contents)
    (empty : ∀ role, role.val = 0 ∨ 21 ≤ role.val → contents role = []) :
    Ready input initial [] contents := by
  refine ⟨⟨registers,bank,?_,Log.initial_refines,?_,?_⟩,?_⟩
  · simpa only [Log.encodeHistory,List.reverse_nil,List.flatMap_nil] using empty 21 (Or.inr (by decide))
  · simpa only [initial,List.flatMap_nil,List.reverse_nil] using empty 22 (Or.inr (by decide))
  · simpa only [initial,List.length_nil,List.replicate_zero] using empty 23 (Or.inr (by decide))
  · intro role work
    apply empty role
    rcases work with zero | large
    · exact Or.inl zero
    · exact Or.inr (by omega)

end PDROC.BitVM.VM.Source
