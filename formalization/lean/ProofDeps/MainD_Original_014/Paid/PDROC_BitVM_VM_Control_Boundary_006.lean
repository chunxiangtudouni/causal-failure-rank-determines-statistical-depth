module

public import Paid.PDROC_BitVM_VM_Control_LocalReturn_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.Control.Indirect

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal

theorem state_at_label (code : Program) (state : State code) (label : Label code)
    (position : state.l = some label) : state = ⟨some label, state.var, state.stk⟩ := by
  rcases state with ⟨current, store, contents⟩
  change current = some label at position
  subst current
  rfl

/-- The exact original register read/restore macro. query is only a
specification of actual26 DATA; no Nat is introduced into finite Store. -/
theorem natural_pointer_call (code : Program) (pointer : Register) (query : Nat)
    (store : Store code) (contents : Stack → List Bool)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query)) (scratch : contents 24 = []) :
    ∃ after : State code, ∃ path : Path code pointer
      (atEntry code (.inl .pointer) store contents) after,
      after.l = some (returned code (.inl .pointer)) ∧
      after.stk = Function.update contents 26 (encodeNatBits query ++ contents 26) ∧
      selected code after.var = selected code store ∧ typedFlag code after.var = true ∧
      path.posts.length + 1 = 2 * (encodeNatBits query).length + 7 := by
  obtain ⟨run, final, head, chain, last, halt, _, finalVar, data, length⟩ :=
    Log.HeapPointer.natural_runs pointer query contents (store (.inl .pointer)) register scratch
  obtain ⟨after, path, label, physical, flags, count⟩ :=
    local_return code pointer (.inl .pointer) store contents run final head chain last halt
  refine ⟨after, path, label, physical.trans data, ?_, ?_, count.trans length⟩
  · rw [flags]
    exact selected_frame code .pointer final.var store
  · change Log.Query.equality (after.var (.inl .pointer)).2.1 = true
    rw [flags, split_self, finalVar]
    rfl

/-- Wrong original Cell type is really rejected by the old peek/tag
guard, with the entire physical caller data retained byte for byte. -/
theorem rational_pointer_call (code : Program) (pointer : Register) (query : Rat)
    (store : Store code) (contents : Stack → List Bool)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational query)) :
    ∃ after : State code, ∃ path : Path code pointer
      (atEntry code (.inl .pointer) store contents) after,
      after.l = some (returned code (.inl .pointer)) ∧ after.stk = contents ∧
      selected code after.var = selected code store ∧ typedFlag code after.var = false ∧
      path.posts.length = 2 := by
  obtain ⟨run, final, head, chain, last, halt, _, finalVar, data, length⟩ :=
    Log.HeapPointer.rational_runs pointer query contents (store (.inl .pointer)) register
  obtain ⟨after, path, label, physical, flags, count⟩ :=
    local_return code pointer (.inl .pointer) store contents run final head chain last halt
  refine ⟨after, path, label, physical.trans data, ?_, ?_, ?_⟩
  · rw [flags]
    exact selected_frame code .pointer final.var store
  · change Log.Query.equality (after.var (.inl .pointer)).2.1 = false
    rw [flags, split_self, finalVar]
    rfl
  · have total : path.posts.length + 1 = 3 := count.trans length
    omega

theorem reset_resume (code : Program) (pointer : Register) (store : Store code) (contents : Stack → List Bool) :
    TM2.step (program code pointer)
      (⟨some (returned code (selectedIndex code)), store, contents⟩ : State code) =
      some (atEntry code (.inl (.initialClear 0)) store contents) := rfl

theorem literal_resume (code : Program) (pointer : Register) (candidate : PC code)
    (store : Store code) (contents : Stack → List Bool) :
    TM2.step (program code pointer)
      (⟨some (returned code (.inl (.literal candidate))), store, contents⟩ : State code) =
      some (atEntry code (.inl (.compare candidate)) store contents) := rfl

theorem typed_pointer_resume (code : Program) (pointer : Register)
    (store : Store code) (contents : Stack → List Bool) (typed : typedFlag code store = true) :
    TM2.step (program code pointer)
      (⟨some (returned code (.inl .pointer)), store, contents⟩ : State code) =
      some ⟨some (((literalPC code 0).map (fun point => entry code (.inl (.literal point)))).getD (cleanupEntry code)),
        store, contents⟩ := by
  change some (TM2.stepAux (resume code (.inl .pointer)) store contents) = _
  simp only [resume, TM2.stepAux, typed, goCandidate]
  rfl

theorem invalid_pointer_resume (code : Program) (pointer : Register)
    (store : Store code) (contents : Stack → List Bool) (invalid : typedFlag code store = false) :
    TM2.step (program code pointer)
      (⟨some (returned code (.inl .pointer)), store, contents⟩ : State code) =
      some ⟨some (cleanupEntry code), store, contents⟩ := by
  change some (TM2.stepAux (resume code (.inl .pointer)) store contents) = _
  simp only [resume, TM2.stepAux, invalid]
  rfl

theorem initial_clear_resume (code : Program) (pointer : Register) (slot : Fin 4)
    (bound : slot.val + 1 < 4) (store : Store code) (contents : Stack → List Bool) :
    TM2.step (program code pointer)
      (⟨some (returned code (.inl (.initialClear slot))), store, contents⟩ : State code) =
      some (atEntry code (.inl (.initialClear ⟨slot.val + 1, bound⟩)) store contents) := by
  change some (TM2.stepAux (resume code (.inl (.initialClear slot))) store contents) = _
  simp only [resume, dite_eq_left bound, TM2.stepAux]
  rfl

theorem initial_last_resume (code : Program) (pointer : Register) (store : Store code) (contents : Stack → List Bool) :
    TM2.step (program code pointer)
      (⟨some (returned code (.inl (.initialClear 3))), store, contents⟩ : State code) =
      some (atEntry code (.inl .pointer) store contents) := rfl

theorem final_clear_resume (code : Program) (pointer : Register) (slot : Fin 4)
    (bound : slot.val + 1 < 4) (store : Store code) (contents : Stack → List Bool) :
    TM2.step (program code pointer)
      (⟨some (returned code (.inl (.finalClear slot))), store, contents⟩ : State code) =
      some (atEntry code (.inl (.finalClear ⟨slot.val + 1, bound⟩)) store contents) := by
  change some (TM2.stepAux (resume code (.inl (.finalClear slot))) store contents) = _
  simp only [resume, dite_eq_left bound, TM2.stepAux]
  rfl

theorem final_halt_resume (code : Program) (pointer : Register) (store : Store code) (contents : Stack → List Bool) :
    TM2.step (program code pointer)
      (⟨some (returned code (.inl (.finalClear 3))), store, contents⟩ : State code) =
      some ⟨none, store, contents⟩ := rfl

end PDROC.BitVM.VM.Control.Indirect
