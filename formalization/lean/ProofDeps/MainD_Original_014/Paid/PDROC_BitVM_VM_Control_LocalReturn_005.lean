module

public import Paid.PDROC_BitVM_VM_Control_Indirect_004
public import Paid.PDROC_BitVM_Common_IO_Paths_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.Control.Indirect

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Common.IO

abbrev Path (code : Program) (pointer : Register) := ActualPath (TM2.step (program code pointer))

def saved (code : Program) (index : Index code) (store : Store code) :
    Kernel.CallFamily.Saved (LocalStore code) index := fun other => store other.val

def localBefore (code : Program) (index : Index code) (store : Store code) (contents : Stack → List Bool) :
    TM2.Cfg Alphabet (LocalLabel code index) (LocalStore code index) :=
  ⟨some (startLabel code index), store index, contents⟩

def atEntry (code : Program) (index : Index code) (store : Store code) (contents : Stack → List Bool) : State code :=
  ⟨some (entry code index), store, contents⟩

theorem split_original (code : Program) (index : Index code) (store : Store code) :
    Kernel.CallFamily.split (LocalStore code) index (store index, saved code index store) = store :=
  (Equiv.piSplitAt index (LocalStore code)).symm_apply_apply store

theorem split_other (code : Program) (index other : Index code) (different : other ≠ index)
    (value : LocalStore code index) (store : Store code) :
    Kernel.CallFamily.split (LocalStore code) index (value, saved code index store) other = store other := by
  change (if same : other = index then same.symm.rec value else store other) = store other
  exact dite_eq_right different

theorem split_self (code : Program) (index : Index code)
    (value : LocalStore code index) (store : Store code) :
    Kernel.CallFamily.split (LocalStore code) index (value, saved code index store) index = value :=
  congrArg Prod.fst ((Equiv.piSplitAt index (LocalStore code)).apply_symm_apply (value, saved code index store))

theorem selected_frame (code : Program) (operation : Macro code)
    (value : LocalStore code (.inl operation)) (store : Store code) :
    selected code (Kernel.CallFamily.split (LocalStore code) (.inl operation)
      (value, saved code (.inl operation) store)) = selected code store := by
  exact split_other code (.inl operation) (selectedIndex code) (by simp [selectedIndex]) value store

theorem embedded_before (code : Program) (index : Index code) (store : Store code) (contents : Stack → List Bool) :
    Kernel.CallFamily.cfg (LocalLabel code) (LocalStore code) index (saved code index store)
      (localBefore code index store contents) = atEntry code index store contents := by
  change (⟨some (entry code index),
    Kernel.CallFamily.split (LocalStore code) index (store index, saved code index store), contents⟩ : State code) = _
  rw [split_original]
  rfl

/-- Adapt a selected real source run to the existing duplicate-free path
type. Only proof data is packed; no new transition or run oracle is used. -/
theorem path_of_run {S : Type*} (step : S → Option S) (run : List S) (before after : S)
    (head : run.head? = some before)
    (chain : run.IsChain (fun x y => step x = some y)) (last : run.getLast? = some after) :
    ∃ path : ActualPath step before after, path.posts.length + 1 = run.length := by
  cases run with
  | nil => cases head
  | cons first posts =>
    have same : first = before := Option.some.inj head
    subst first
    exact ⟨⟨posts, chain, last⟩, rfl⟩

/-- One exact CallFamily022 lift, on the SAME source trace and tape.
The macro's true source HALT is a real caller return, not whole-VM HALT.
No store is initialized for free: all its other fields are actual carry. -/
theorem local_return (code : Program) (pointer : Register) (index : Index code)
    (store : Store code) (contents : Stack → List Bool)
    (run : List (TM2.Cfg Alphabet (LocalLabel code index) (LocalStore code index)))
    (final : TM2.Cfg Alphabet (LocalLabel code index) (LocalStore code index))
    (head : run.head? = some (localBefore code index store contents))
    (chain : run.IsChain (fun before after => TM2.step (source code pointer index) before = some after))
    (last : run.getLast? = some final) (halt : TM2.step (source code pointer index) final = none) :
    ∃ after : State code, ∃ path : Path code pointer (atEntry code index store contents) after,
      after.l = some (returned code index) ∧ after.stk = final.stk ∧
      after.var = Kernel.CallFamily.split (LocalStore code) index (final.var, saved code index store) ∧
      path.posts.length + 1 = run.length := by
  obtain ⟨actual, after, first, actualChain, actualLast, label, data, flags, length⟩ :=
    Kernel.CallFamily.actual_return_trace (LocalLabel code) (LocalStore code) (source code pointer) (resume code)
      index (saved code index store) run (localBefore code index store contents) final head chain last halt
  rw [embedded_before] at first
  obtain ⟨path, count⟩ := path_of_run (TM2.step (program code pointer)) actual
    (atEntry code index store contents) after first actualChain actualLast
  exact ⟨after, path, label, data, flags, count.trans length⟩

theorem reset_call (code : Program) (pointer : Register) (store : Store code) (contents : Stack → List Bool) :
    ∃ after : State code, ∃ path : Path code pointer
      (atEntry code (selectedIndex code) store contents) after,
      after.l = some (returned code (selectedIndex code)) ∧ after.stk = contents ∧
      selected code after.var = none ∧ path.posts.length = 1 := by
  let before := localBefore code (selectedIndex code) store contents
  let final : TM2.Cfg Alphabet Unit (Option (PC code)) := ⟨none, none, contents⟩
  have edge : TM2.step (source code pointer (selectedIndex code)) before = some final := rfl
  have chain : [before, final].IsChain
      (fun x y => TM2.step (source code pointer (selectedIndex code)) x = some y) :=
    List.isChain_cons_cons.mpr ⟨edge, List.isChain_singleton _⟩
  obtain ⟨after, path, label, data, flags, count⟩ := local_return code pointer (selectedIndex code)
    store contents [before, final] final rfl chain rfl rfl
  refine ⟨after, path, label, data, ?_, ?_⟩
  · rw [flags]
    exact split_self code (selectedIndex code) none store
  · change path.posts.length + 1 = 2 at count
    omega

theorem initial_clear_call (code : Program) (pointer : Register) (slot : Fin 4)
    (store : Store code) (contents : Stack → List Bool) :
    ∃ after : State code, ∃ path : Path code pointer
      (atEntry code (.inl (.initialClear slot)) store contents) after,
      after.l = some (returned code (.inl (.initialClear slot))) ∧
      after.stk = Function.update contents (clearSlot slot) [] ∧
      selected code after.var = selected code store ∧ path.posts.length + 1 = (contents (clearSlot slot)).length + 3 := by
  obtain ⟨run, final, head, chain, last, halt, _, _, data, length⟩ :=
    Log.HeapClear.runs (clearSlot slot) contents (store (.inl (.initialClear slot)))
  obtain ⟨after, path, label, physical, flags, count⟩ :=
    local_return code pointer (.inl (.initialClear slot)) store contents run final head chain last halt
  refine ⟨after, path, label, physical.trans data, ?_, count.trans length⟩
  rw [flags]
  exact selected_frame code (.initialClear slot) final.var store

theorem final_clear_call (code : Program) (pointer : Register) (slot : Fin 4)
    (store : Store code) (contents : Stack → List Bool) :
    ∃ after : State code, ∃ path : Path code pointer
      (atEntry code (.inl (.finalClear slot)) store contents) after,
      after.l = some (returned code (.inl (.finalClear slot))) ∧
      after.stk = Function.update contents (clearSlot slot) [] ∧
      selected code after.var = selected code store ∧ path.posts.length + 1 = (contents (clearSlot slot)).length + 3 := by
  obtain ⟨run, final, head, chain, last, halt, _, _, data, length⟩ :=
    Log.HeapClear.runs (clearSlot slot) contents (store (.inl (.finalClear slot)))
  obtain ⟨after, path, label, physical, flags, count⟩ :=
    local_return code pointer (.inl (.finalClear slot)) store contents run final head chain last halt
  refine ⟨after, path, label, physical.trans data, ?_, count.trans length⟩
  rw [flags]
  exact selected_frame code (.finalClear slot) final.var store

theorem literal_call (code : Program) (pointer : Register) (candidate : PC code)
    (store : Store code) (contents : Stack → List Bool) (scratch : contents 28 = []) :
    ∃ after : State code, ∃ path : Path code pointer
      (atEntry code (.inl (.literal candidate)) store contents) after,
      after.l = some (returned code (.inl (.literal candidate))) ∧
      after.stk = Function.update contents 24 (encodeNatBits candidate.val) ∧
      selected code after.var = selected code store ∧ path.posts.length + 1 = (contents 24).length + 3 := by
  obtain ⟨run, final, head, chain, last, halt, _, _, data, length⟩ :=
    PCLiteral.pc_runs code candidate contents (store (.inl (.literal candidate))) scratch
  obtain ⟨after, path, label, physical, flags, count⟩ :=
    local_return code pointer (.inl (.literal candidate)) store contents run final head chain last halt
  refine ⟨after, path, label, physical.trans data, ?_, count.trans length⟩
  rw [flags]
  exact selected_frame code (.literal candidate) final.var store

theorem comparison_call (code : Program) (pointer : Register) (candidate : PC code) (query : Nat)
    (store : Store code) (contents : Stack → List Bool)
    (address : contents 24 = encodeNatBits candidate.val) (queryValue : contents 26 = encodeNatBits query)
    (scratch : contents 27 = []) :
    ∃ after : State code, ∃ path : Path code pointer
      (atEntry code (.inl (.compare candidate)) store contents) after,
      after.l = some (returned code (.inl (.compare candidate))) ∧
      after.stk = Log.InputCompare.compared contents ∧
      selected code after.var = selected code store ∧
      equalityFlag code candidate after.var = decide (candidate.val = query) ∧
      path.posts.length + 1 ≤ 4 * natBits candidate.val + 8 := by
  obtain ⟨run, final, head, chain, last, halt, _, _, equal, _, data, length⟩ :=
    Log.InputCompare.runs candidate.val query contents (store (.inl (.compare candidate))) address queryValue scratch
  obtain ⟨after, path, label, physical, flags, count⟩ :=
    local_return code pointer (.inl (.compare candidate)) store contents run final head chain last halt
  refine ⟨after, path, label, physical.trans data, ?_, ?_, count.trans_le length⟩
  · rw [flags]
    exact selected_frame code (.compare candidate) final.var store
  · change Log.Query.equality (after.var (.inl (.compare candidate))).2.1 = _
    rw [flags, split_self]
    exact equal

end PDROC.BitVM.VM.Control.Indirect
