module

public import Paid.PDROC_BitVM_VM_ISA_Specification_003
public import Paid.PDROC_BitVM_Log_HeapLoad_042
public import Paid.PDROC_BitVM_Log_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.HeapRefinement

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Source-only integration of the already checked actual opcode programs.
These adapters select each original macro path exactly once. Scratch is
not claimed empty afterwards: the separate genuine cleaner produces Ready.
No StepRefinement here is yet a compiler-pass or a full-VM claim. -/

private theorem high_not_register (destination : Register) (role : Stack) (high : 21 ≤ role.val) :
    role ≠ registerSlot destination := by
  intro equal
  have values := congrArg Fin.val equal
  have bounds := registerSlot_bounds destination
  omega

theorem inputLoad_step (backend : RatBackend) (core : Bool) (destination pointer : Register) :
    StepRefinement backend core ⟨.loadInput destination pointer, rfl⟩ := by
  intro input logical next events contents size ready success
  let physical : Log.InputLoad.State := ⟨some Log.InputLoad.startLabel, default, contents⟩
  obtain ⟨query, value, run, final, natural, answer, nextValue, head, chain, last, halt,
      done, flag, registers, bank, frame, time⟩ :=
    Log.InputLoad.load_step_refinement core input logical next pointer destination physical rfl
      ready.registers size ready.bank success
  have history : final.stk 21 = contents 21 :=
    frame 21 (Or.inl (by decide)) (high_not_register destination 21 (by decide))
  have word : final.stk 22 = contents 22 :=
    frame 22 (Or.inl (by decide)) (high_not_register destination 22 (by decide))
  have ticks : final.stk 23 = contents 23 :=
    frame 23 (Or.inl (by decide)) (high_not_register destination 23 (by decide))
  have output : next.output = logical.output := by rw [nextValue]; rfl
  have heap : Log.Refines events next := by
    simpa only [Log.eventOf, Option.toList_none, List.append_nil] using
      Log.execute_refines input (.loadInput destination pointer) events logical next ready.heap success
  refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
  simp only [Log.eventOf, Option.toList_none, List.append_nil]
  refine ⟨registers, bank, history.trans ready.history, heap, ?_, ?_⟩
  · rw [word, ready.outputWord, output]
  · rw [ticks, ready.outputTicks, output]

theorem load_step (backend : RatBackend) (core : Bool) (destination pointer : Register) :
    StepRefinement backend core ⟨.load destination pointer, rfl⟩ := by
  intro input logical next events contents size ready success
  let physical : Log.HeapLoad.State := ⟨some Log.HeapLoad.startLabel, default, contents⟩
  obtain ⟨query, value, run, final, natural, answer, nextValue, head, chain, last, halt,
      done, flag, heap, registers, history, frame, time⟩ :=
    Log.HeapLoad.load_step_refinement input logical next events pointer destination physical rfl
      ready.registers ready.history ready.heap success
  have bank : Log.InputLoad.BankAt input final.stk := by
    intro field
    have low : (Log.BankDrain.bankSlot field).val < 24 := by
      change field.val + 1 < 24
      omega
    exact (frame (Log.BankDrain.bankSlot field) (Or.inl low)
      (Log.BankDrain.bankSlot_ne field (registerSlot destination)
        (Or.inr (registerSlot_bounds destination).1))).trans (ready.bank field)
  have word : final.stk 22 = contents 22 :=
    frame 22 (Or.inl (by decide)) (high_not_register destination 22 (by decide))
  have ticks : final.stk 23 = contents 23 :=
    frame 23 (Or.inl (by decide)) (high_not_register destination 23 (by decide))
  have output : next.output = logical.output := by rw [nextValue]; rfl
  refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
  simp only [Log.eventOf, Option.toList_none, List.append_nil]
  refine ⟨registers, bank, history, heap, ?_, ?_⟩
  · rw [word, ready.outputWord, output]
  · rw [ticks, ready.outputTicks, output]

end PDROC.BitVM.VM.ISA.HeapRefinement
