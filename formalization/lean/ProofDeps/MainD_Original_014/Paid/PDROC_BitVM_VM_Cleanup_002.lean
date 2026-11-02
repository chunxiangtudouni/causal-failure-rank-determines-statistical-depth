module

public import Paid.PDROC_BitVM_VM_Cleanup_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.VM.Cleanup

open Turing PDROC.BitVM.Native PDROC.BitVM.Common.IO
open PaperProofs.Common.Native.PSTRWordBool

def entry (count : ℕ) (bound : count ≤ 9) : Label := ⟨count, by omega⟩

def flagsAfter {Saved : Type*} (count : ℕ) (store : Store Saved) : Store Saved :=
  if count = 0 then store else (none, store.2)

theorem flagsAfter_succ {Saved : Type*} (count : ℕ) (store : Store Saved) :
    (none, (flagsAfter count store).2) = flagsAfter (count + 1) store := by
  by_cases zero : count = 0 <;> simp [flagsAfter, zero]

/-! Induction only selects and joins the nine pre-existing finite labels.
No Nat counter, fuel or prior workspace bound is a machine-state field. -/
theorem clear_path (Saved : Type*) (contents : Stack → List Bool) (store : Store Saved) :
    ∀ (count : ℕ) (bound : count ≤ 9),
    ∃ path : ActualPath (TM2.step (program Saved))
      (⟨some startLabel, store, contents⟩ : State Saved)
      (⟨some (entry count bound), flagsAfter count store, clearedData count contents⟩ : State Saved),
      path.posts.length ≤ count * (dataSize contents + 2) := by
  intro count
  induction count with
  | zero =>
    intro bound
    rw [clearedData_zero]
    refine ⟨ActualPath.refl _, ?_⟩
    simp only [ActualPath.refl, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | succ count ih =>
    intro bound
    have inside : count < 9 := by omega
    let stage : Fin 9 := ⟨count, inside⟩
    obtain ⟨left, leftLength⟩ := ih (by omega)
    obtain ⟨right, rightLength⟩ := stage_path Saved stage (clearedData count contents) (flagsAfter count store)
    rw [← clearedData_step stage contents, ← flagsAfter_succ count store]
    refine ⟨left.trans right, ?_⟩
    have actualCurrent : clearedData count contents (slot stage) = contents (slot stage) :=
      clearedData_current stage contents
    rw [actualCurrent] at rightLength
    have small := word_le_dataSize contents (slot stage)
    change (left.posts ++ right.posts).length ≤ (count + 1) * (dataSize contents + 2)
    simp only [List.length_append, Nat.add_mul, Nat.one_mul]
    omega

theorem done_step (Saved : Type*) (contents : Stack → List Bool) (store : Store Saved) :
    TM2.step (program Saved)
      (⟨some (entry 9 (by omega)), flagsAfter 9 store, clearedData 9 contents⟩ : State Saved) =
      some (⟨none, (none, store.2), cleaned contents⟩ : State Saved) := by
  rw [clearedData_nine]
  rfl

/-- Same selected caller trace, including a real final HALT. Input roles
1..23 are protected, with arbitrary old data in every physical role. The
single OptionBool scratch flag is reset; all finite Saved carry survives. -/
theorem runs (Saved : Type*) (before : State Saved) (position : before.l = some startLabel) :
    ∃ (trace : List (State Saved)) (after : State Saved),
      trace.head? = some before ∧ trace.IsChain (fun a b => TM2.step (program Saved) a = some b) ∧
      trace.getLast? = some after ∧ TM2.step (program Saved) after = none ∧ after.l = none ∧
      after.var = (none, before.var.2) ∧ after.stk = cleaned before.stk ∧
      (∀ role : Stack, 1 ≤ role.val ∧ role.val < 24 → after.stk role = before.stk role) ∧
      (∀ role : Stack, isWork role → after.stk role = []) ∧
      trace.length ≤ 20 * (dataSize before.stk + 1) ∧
      (∀ state ∈ trace, ∀ role : Stack, (state.stk role).length ≤ dataSize before.stk) := by
  obtain ⟨initialPath, initialLength⟩ := clear_path Saved before.stk before.var 9 (by omega)
  let final : State Saved := ⟨none, (none, before.var.2), cleaned before.stk⟩
  let path := initialPath.trans (ActualPath.single (done_step Saved before.stk before.var))
  let first : State Saved := ⟨some startLabel, before.var, before.stk⟩
  let trace := first :: path.posts
  have head : trace.head? = some before := by
    rcases before with ⟨currentLabel, currentStore, currentData⟩
    change currentLabel = some startLabel at position
    subst currentLabel
    rfl
  have chain : trace.IsChain (fun a b => TM2.step (program Saved) a = some b) := path.chain
  have last : trace.getLast? = some final := path.last
  have length : trace.length ≤ 20 * (dataSize before.stk + 1) := by
    simp only [trace, List.length_cons, path, ActualPath.trans_length, ActualPath.single,
      List.length_cons, List.length_nil]
    omega
  have supported : first.l ∈ Finset.insertNone (Finset.univ : Finset Label) :=
    Finset.some_mem_insertNone.mpr (Finset.mem_univ _)
  have occupied := PDROC.BitVM.Common.source_path_occupancy (program Saved)
    (Finset.univ : Finset Label) (supports Saved) first path.posts (dataSize before.stk)
    supported (word_le_dataSize before.stk) chain
  refine ⟨trace, final, head, chain, last, rfl, rfl, rfl, rfl, ?_, ?_, length, ?_⟩
  · intro role safeRole
    exact cleaned_frame before.stk role safeRole
  · intro role work
    exact cleaned_work before.stk role work
  · intro state member role
    have actual := (occupied state member).2 role
    simpa only [sourcePushCap_zero, Nat.zero_mul, Nat.add_zero] using actual

/-- Every nested statement snapshot along that SAME trace has the same
entry-data envelope: the cleaner has syntactically zero pushes. -/
theorem internal_space (Saved : Type*) (before : State Saved) (trace : List (State Saved))
    (occupied : ∀ state ∈ trace, ∀ role : Stack, (state.stk role).length ≤ dataSize before.stk) :
    ∀ state ∈ trace, ∀ label, state.l = some label →
      ∀ snapshot ∈ AuxWorkspace.nodes (program Saved label) state.var state.stk,
        ∀ role : Stack, (snapshot.2 role).length ≤ dataSize before.stk := by
  intro state member label position snapshot visited role
  have bound := AuxWorkspace.node_bound (program Saved label) state.var state.stk (dataSize before.stk)
    (occupied state member) snapshot visited role
  simpa only [pushes_zero, Nat.add_zero] using bound

end PDROC.BitVM.VM.Cleanup
