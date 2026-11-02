module

public import Paid.PDROC_BitVM_VM_Control_Boundary_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.Control.Indirect

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Common.IO

def cleared (contents : Stack → List Bool) : Stack → List Bool :=
  Function.update (Function.update (Function.update (Function.update contents 24 []) 26 []) 27 []) 28 []

def scratchCost (contents : Stack → List Bool) : Nat :=
  (contents 24).length + (contents 26).length + (contents 27).length + (contents 28).length

theorem cleared_empty (contents : Stack → List Bool) (slot : Fin 4) : cleared contents (clearSlot slot) = [] := by
  fin_cases slot <;> simp [cleared, clearSlot]

theorem cleared_other (contents : Stack → List Bool) (slot : Stack)
    (outside : ∀ index : Fin 4, slot ≠ clearSlot index) : cleared contents slot = contents slot := by
  have a : slot ≠ 24 := by simpa [clearSlot] using outside 0
  have b : slot ≠ 26 := by simpa [clearSlot] using outside 1
  have c : slot ≠ 27 := by simpa [clearSlot] using outside 2
  have d : slot ≠ 28 := by simpa [clearSlot] using outside 3
  simp [cleared, Function.update_of_ne a, Function.update_of_ne b,
    Function.update_of_ne c, Function.update_of_ne d]

def clearMacro (code : Program) : Bool → Fin 4 → Macro code
  | false, slot => .initialClear slot
  | true, slot => .finalClear slot

def clearExit (code : Program) (finish : Bool) (slot : Fin 4) : Option (Label code) :=
  if bound : slot.val + 1 < 4 then some (entry code (.inl (clearMacro code finish ⟨slot.val + 1, bound⟩)))
  else if finish then none else some (entry code (.inl .pointer))

theorem clear_call (code : Program) (pointer : Register) (finish : Bool) (slot : Fin 4)
    (store : Store code) (contents : Stack → List Bool) :
    ∃ after : State code, ∃ path : Path code pointer
      (atEntry code (.inl (clearMacro code finish slot)) store contents) after,
      after.l = some (returned code (.inl (clearMacro code finish slot))) ∧
      after.stk = Function.update contents (clearSlot slot) [] ∧
      selected code after.var = selected code store ∧ path.posts.length + 1 = (contents (clearSlot slot)).length + 3 := by
  cases finish with
  | false => exact initial_clear_call code pointer slot store contents
  | true => exact final_clear_call code pointer slot store contents

theorem clear_resume (code : Program) (pointer : Register) (finish : Bool) (slot : Fin 4)
    (store : Store code) (contents : Stack → List Bool) :
    TM2.step (program code pointer)
      (⟨some (returned code (.inl (clearMacro code finish slot))), store, contents⟩ : State code) =
      some ⟨clearExit code finish slot, store, contents⟩ := by
  cases finish with
  | false =>
    by_cases bound : slot.val + 1 < 4
    · simpa only [clearMacro, clearExit, dite_eq_left bound, atEntry] using
        initial_clear_resume code pointer slot bound store contents
    · have last : slot = 3 := by apply Fin.ext; have cap := slot.isLt; dsimp; omega
      subst slot
      exact initial_last_resume code pointer store contents
  | true =>
    by_cases bound : slot.val + 1 < 4
    · simpa only [clearMacro, clearExit, dite_eq_left bound, atEntry] using
        final_clear_resume code pointer slot bound store contents
    · have last : slot = 3 := by apply Fin.ext; have cap := slot.isLt; dsimp; omega
      subst slot
      exact final_halt_resume code pointer store contents

/-- One old genuine clear run followed by its REAL caller dispatch.
No scratch-empty premise is used; every old byte is physically popped. -/
theorem clear_stage (code : Program) (pointer : Register) (finish : Bool) (slot : Fin 4)
    (store : Store code) (contents : Stack → List Bool) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (.inl (clearMacro code finish slot)) store contents)
      ⟨clearExit code finish slot, nextStore, Function.update contents (clearSlot slot) []⟩,
      selected code nextStore = selected code store ∧ path.posts.length = (contents (clearSlot slot)).length + 3 := by
  obtain ⟨after, path, label, data, flags, count⟩ := clear_call code pointer finish slot store contents
  rcases after with ⟨actualLabel, nextStore, actualData⟩
  change actualLabel = some (returned code (.inl (clearMacro code finish slot))) at label
  change actualData = Function.update contents (clearSlot slot) [] at data
  subst actualLabel; subst actualData
  have edge := clear_resume code pointer finish slot nextStore (Function.update contents (clearSlot slot) [])
  let joined := path.trans (ActualPath.single edge)
  refine ⟨nextStore, joined, flags, ?_⟩
  exact (ActualPath.trans_length path (ActualPath.single edge)).trans count

/-- Four actual physical clear macros in one selected trace, including
every source return and goto/HALT. Initial clear ends at the pointer read;
final clear actually HALTs the local macro so the parent can return it.
The finite selected flag survives ALL four real clear passes. -/
theorem clears_path (code : Program) (pointer : Register) (finish : Bool)
    (store : Store code) (contents : Stack → List Bool) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (.inl (clearMacro code finish 0)) store contents)
      ⟨if finish then none else some (entry code (.inl .pointer)), nextStore, cleared contents⟩,
      selected code nextStore = selected code store ∧ path.posts.length = scratchCost contents + 12 := by
  let c1 := Function.update contents (24 : Stack) []
  let c2 := Function.update c1 (26 : Stack) []
  let c3 := Function.update c2 (27 : Stack) []
  obtain ⟨s1, p1, f1, n1⟩ := clear_stage code pointer finish 0 store contents
  let first : Path code pointer (atEntry code (.inl (clearMacro code finish 0)) store contents)
      (atEntry code (.inl (clearMacro code finish 1)) s1 c1) := p1
  obtain ⟨s2, p2, f2, n2⟩ := clear_stage code pointer finish 1 s1 c1
  let second : Path code pointer (atEntry code (.inl (clearMacro code finish 1)) s1 c1)
      (atEntry code (.inl (clearMacro code finish 2)) s2 c2) := p2
  obtain ⟨s3, p3, f3, n3⟩ := clear_stage code pointer finish 2 s2 c2
  let third : Path code pointer (atEntry code (.inl (clearMacro code finish 2)) s2 c2)
      (atEntry code (.inl (clearMacro code finish 3)) s3 c3) := p3
  obtain ⟨s4, p4, f4, n4⟩ := clear_stage code pointer finish 3 s3 c3
  let fourth : Path code pointer (atEntry code (.inl (clearMacro code finish 3)) s3 c3)
      ⟨if finish then none else some (entry code (.inl .pointer)), s4, cleared contents⟩ := p4
  let joined := ((first.trans second).trans third).trans fourth
  refine ⟨s4, joined, f4.trans (f3.trans (f2.trans f1)), ?_⟩
  have a : first.posts.length = (contents 24).length + 3 := n1
  have b : second.posts.length = (contents 26).length + 3 := by simpa [c1, clearSlot] using n2
  have c : third.posts.length = (contents 27).length + 3 := by simpa [c2, c1, clearSlot] using n3
  have d : fourth.posts.length = (contents 28).length + 3 := by simpa [c3, c2, c1, clearSlot] using n4
  have sum : joined.posts.length = first.posts.length + second.posts.length + third.posts.length + fourth.posts.length := by
    simp only [joined, ActualPath.trans, List.length_append]
  rw [sum, a, b, c, d]
  unfold scratchCost
  omega

/-- Actual finite-flag reset and the entire initial physical cleanup.
No caller scratch bounds or empty-workspace qualification is introduced. -/
theorem prologue_path (code : Program) (pointer : Register) (store : Store code) (contents : Stack → List Bool) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (selectedIndex code) store contents)
      (atEntry code (.inl .pointer) nextStore (cleared contents)),
      selected code nextStore = none ∧ path.posts.length = scratchCost contents + 14 := by
  obtain ⟨after, reset, label, data, flags, count⟩ := reset_call code pointer store contents
  rcases after with ⟨actualLabel, s1, actualData⟩
  change actualLabel = some (returned code (selectedIndex code)) at label
  change actualData = contents at data
  subst actualLabel; subst actualData
  have edge := reset_resume code pointer s1 contents
  obtain ⟨s2, clear, carry, length⟩ := clears_path code pointer false s1 contents
  let tail : Path code pointer (atEntry code (.inl (.initialClear 0)) s1 contents)
      (atEntry code (.inl .pointer) s2 (cleared contents)) := clear
  let joined := (reset.trans (ActualPath.single edge)).trans tail
  refine ⟨s2, joined, carry.trans flags, ?_⟩
  have tailLength : tail.posts.length = scratchCost contents + 12 := length
  simp only [joined, ActualPath.trans, ActualPath.single, List.length_append, List.length_cons, List.length_nil]
  omega

end PDROC.BitVM.VM.Control.Indirect
