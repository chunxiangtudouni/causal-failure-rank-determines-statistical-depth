module

public import Paid.PDROC_BitVM_VM_ISA_HeapRefinement_001
public import Paid.PDROC_BitVM_Log_HeapStore_031
public import Paid.PDROC_BitVM_Log_HeapRelease_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.HeapRefinement

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-! The exact chronological source event is appended to the logical list;
the already checked macro actually prepends its canonical bytes to stack21.
Replay-equivalent histories are not substituted for this exact history. -/

theorem store_step (backend : RatBackend) (core : Bool) (pointer source : Register) :
    StepRefinement backend core ⟨.store pointer source, rfl⟩ := by
  intro input logical next events contents size ready success
  cases pointerValue : logical.register pointer with
  | rational value => simp [Instruction.execute, pointerValue, Cell.nat?] at success
  | natural address =>
    have nextValue : next = Log.HeapStore.ramStored logical address source :=
      Option.some.inj (success.symm.trans (Log.HeapStore.execute_store_nat input logical pointer source address pointerValue))
    subst next
    let physical : Log.HeapStore.State := ⟨some Log.HeapStore.startLabel, default, contents⟩
    obtain ⟨run, final, head, chain, last, halt, done, flag, executed, heap, registers, history, frame, time⟩ :=
      Log.HeapStore.store_natural_refinement input logical events pointer source address physical rfl
        ready.registers ready.history ready.heap pointerValue
    have bank : Log.InputLoad.BankAt input final.stk := by
      intro field
      exact (frame (Log.BankDrain.bankSlot field)
        (Log.BankDrain.bankSlot_ne field 21 (by decide))
        (Log.BankDrain.bankSlot_ne field 24 (by decide))
        (Log.BankDrain.bankSlot_ne field 25 (by decide))
        (Log.BankDrain.bankSlot_ne field 26 (by decide))
        (Log.BankDrain.bankSlot_ne field 28 (by decide))).trans (ready.bank field)
    have word : final.stk 22 = contents 22 := frame 22 (by decide) (by decide) (by decide) (by decide) (by decide)
    have ticks : final.stk 23 = contents 23 := frame 23 (by decide) (by decide) (by decide) (by decide) (by decide)
    have output : (Log.HeapStore.ramStored logical address source).output = logical.output := rfl
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    simp only [Log.eventOf, pointerValue, Cell.nat?, Option.map_some, Option.toList_some]
    refine ⟨registers, bank, history, heap, ?_, ?_⟩
    · rw [word, ready.outputWord, output]
    · rw [ticks, ready.outputTicks, output]

theorem release_step (backend : RatBackend) (core : Bool) (pointer : Register) :
    StepRefinement backend core ⟨.release pointer, rfl⟩ := by
  intro input logical next events contents size ready success
  cases pointerValue : logical.register pointer with
  | rational value => simp [Instruction.execute, pointerValue, Cell.nat?] at success
  | natural address =>
    have nextValue : next = Log.HeapRelease.ramReleased logical address :=
      Option.some.inj (success.symm.trans (Log.HeapRelease.execute_release_nat input logical pointer address pointerValue))
    subst next
    let physical : Log.HeapRelease.State := ⟨some Log.HeapRelease.startLabel, default, contents⟩
    obtain ⟨run, final, head, chain, last, halt, done, flag, executed, heap, registers, history, frame, time⟩ :=
      Log.HeapRelease.release_natural_refinement input logical events pointer address physical rfl
        ready.registers ready.history ready.heap pointerValue
    have bank : Log.InputLoad.BankAt input final.stk := by
      intro field
      exact (frame (Log.BankDrain.bankSlot field)
        (Log.BankDrain.bankSlot_ne field 21 (by decide))
        (Log.BankDrain.bankSlot_ne field 24 (by decide))
        (Log.BankDrain.bankSlot_ne field 25 (by decide))
        (Log.BankDrain.bankSlot_ne field 26 (by decide))).trans (ready.bank field)
    have word : final.stk 22 = contents 22 := frame 22 (by decide) (by decide) (by decide) (by decide)
    have ticks : final.stk 23 = contents 23 := frame 23 (by decide) (by decide) (by decide) (by decide)
    have output : (Log.HeapRelease.ramReleased logical address).output = logical.output := rfl
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    simp only [Log.eventOf, pointerValue, Cell.nat?, Option.map_some, Option.toList_some]
    refine ⟨registers, bank, history, heap, ?_, ?_⟩
    · rw [word, ready.outputWord, output]
    · rw [ticks, ready.outputTicks, output]

end PDROC.BitVM.VM.ISA.HeapRefinement
