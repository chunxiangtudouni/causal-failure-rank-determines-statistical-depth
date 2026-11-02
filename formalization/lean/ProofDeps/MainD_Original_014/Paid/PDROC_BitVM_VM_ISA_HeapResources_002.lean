module

public import Paid.PDROC_BitVM_VM_ISA_HeapResources_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.HeapResources

open Turing PaperProofs.Paid.Computation

/-! Constants precede ALL original inputs, logical states, event lists and
old physical tape data. The selected genuine resource path may be compared
to the semantic path by Spec003's full halting-trace uniqueness theorem.
No independent answer/loop/time oracle is an input to these adapters. -/

theorem inputLoad_resource (backend : RatBackend) (core : Bool) (destination pointer : Register) :
    ResourceRefinement backend core ⟨.loadInput destination pointer, rfl⟩ := by
  refine ⟨4096, 2, by decide, by decide, ?_⟩
  intro input logical next events contents size ready success
  let physical : Log.InputLoad.State := ⟨some Log.InputLoad.startLabel, default, contents⟩
  obtain ⟨run, final, head, chain, last, halt, done, flag, registers, bank, frame, time⟩ :=
    Log.InputLoad.load_step_bounded core input logical next pointer destination physical rfl
      ready.registers size ready.bank success
  refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
  exact time.trans (inputLoad_budget input logical events contents ready pointer destination)

theorem load_resource (backend : RatBackend) (core : Bool) (destination pointer : Register) :
    ResourceRefinement backend core ⟨.load destination pointer, rfl⟩ := by
  refine ⟨4096, 2, by decide, by decide, ?_⟩
  intro input logical next events contents size ready success
  let physical : Log.HeapLoad.State := ⟨some Log.HeapLoad.startLabel, default, contents⟩
  obtain ⟨query, value, run, final, natural, answer, nextValue, head, chain, last, halt,
      done, flag, heap, registers, history, frame, time⟩ :=
    Log.HeapLoad.load_step_refinement input logical next events pointer destination physical rfl
      ready.registers ready.history ready.heap success
  refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
  exact time.trans (load_budget input logical events contents ready pointer destination query value natural answer)

theorem store_resource (backend : RatBackend) (core : Bool) (pointer source : Register) :
    ResourceRefinement backend core ⟨.store pointer source, rfl⟩ := by
  refine ⟨4096, 2, by decide, by decide, ?_⟩
  intro input logical next events contents size ready success
  cases pointerValue : logical.register pointer with
  | rational value => simp [Instruction.execute, pointerValue, Cell.nat?] at success
  | natural address =>
    let physical : Log.HeapStore.State := ⟨some Log.HeapStore.startLabel, default, contents⟩
    obtain ⟨run, final, head, chain, last, halt, done, flag, executed, heap, registers, history, frame, time⟩ :=
      Log.HeapStore.store_natural_refinement input logical events pointer source address physical rfl
        ready.registers ready.history ready.heap pointerValue
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    exact time.trans (store_budget input logical events contents ready pointer source address pointerValue)

theorem release_resource (backend : RatBackend) (core : Bool) (pointer : Register) :
    ResourceRefinement backend core ⟨.release pointer, rfl⟩ := by
  refine ⟨4096, 2, by decide, by decide, ?_⟩
  intro input logical next events contents size ready success
  cases pointerValue : logical.register pointer with
  | rational value => simp [Instruction.execute, pointerValue, Cell.nat?] at success
  | natural address =>
    let physical : Log.HeapRelease.State := ⟨some Log.HeapRelease.startLabel, default, contents⟩
    obtain ⟨run, final, head, chain, last, halt, done, flag, executed, heap, registers, history, frame, time⟩ :=
      Log.HeapRelease.release_natural_refinement input logical events pointer address physical rfl
        ready.registers ready.history ready.heap pointerValue
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    exact time.trans (release_budget input logical events contents ready pointer address pointerValue)

end PDROC.BitVM.VM.ISA.HeapResources
