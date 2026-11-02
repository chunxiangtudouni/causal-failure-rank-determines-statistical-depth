module

public import Common.PSTR_WordVM_BankLift_004

/-! ONE actual fixed sixteen-stack caller-linked execution. The source
macro's pre-HALT prefix is embedded, then a genuine goto enters label 3.
No reset, terminal-HALT replacement, or free return is used. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.BankCopy

open Turing

theorem readTrace_active (memory : FieldCopy.Store)
    (word suffix target reverseWord usedWidth : List Bool) :
    ∀ current ∈ FieldCopy.readTrace memory word suffix target reverseWord usedWidth,
      current.l ≠ none := by
  induction word generalizing memory reverseWord usedWidth with
  | nil =>
    intro current present
    simp only [FieldCopy.readTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> intro equality <;> cases equality
  | cons bit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | member
    · subst current
      intro equality
      cases equality
    · exact ih _ _ _ current member

theorem restoreTrace_active (memory : FieldCopy.Store)
    (reverseWord word target width : List Bool) :
    ∀ current ∈ FieldCopy.restoreTrace memory reverseWord word target width,
      current.l ≠ none := by
  induction reverseWord generalizing memory word target width with
  | nil =>
    intro current present
    simp only [FieldCopy.restoreTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> intro equality <;> cases equality
  | cons bit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | member
    · subst current
      intro equality
      cases equality
    · exact ih _ _ _ _ current member

theorem copyPortTrace_active (memory : FieldCopy.Store) (word suffix target : List Bool) :
    ∀ current ∈ FieldCopy.copyPortTrace memory word suffix target, current.l ≠ none := by
  intro current present
  rcases List.mem_append.mp present with outward | returning
  · exact readTrace_active _ _ _ _ _ _ current outward
  · exact restoreTrace_active _ _ _ _ _ current (List.mem_of_mem_tail returning)

def prefixTrace (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) : List State :=
  (FieldCopy.copyPortTrace memory word suffix target).map (configuration background flags)

theorem prefixTrace_head (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (prefixTrace background flags memory word suffix target).head? =
      some (configuration background flags (FieldCopy.copyStart memory word suffix target)) := by
  simp only [prefixTrace, List.head?_map, FieldCopy.copyPortTrace_head, Option.map_some]

theorem prefixTrace_last (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (prefixTrace background flags memory word suffix target).getLast? =
      some (configuration background flags (FieldCopy.copyPort word suffix target)) := by
  simp only [prefixTrace, List.getLast?_map, FieldCopy.copyPortTrace_last, Option.map_some]

theorem prefixTrace_chain (caller : Label → Statement)
    (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (prefixTrace background flags memory word suffix target).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  apply (List.isChain_map (configuration background flags)).mpr
  apply List.IsChain.imp_of_mem_imp _ (FieldCopy.copyPortTrace_chain memory word suffix target)
  intro before after _ member edge
  exact step_configuration caller background flags before after edge
    (copyPortTrace_active _ _ _ _ after member)

def trace (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) : List State :=
  prefixTrace background flags memory word suffix target ++
    [returned background flags word suffix target]

theorem trace_head (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (trace background flags memory word suffix target).head? =
      some (configuration background flags (FieldCopy.copyStart memory word suffix target)) := by
  rw [trace, List.head?_append, prefixTrace_head]
  rfl

theorem trace_last (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (trace background flags memory word suffix target).getLast? =
      some (returned background flags word suffix target) :=
  List.getLast?_append_cons _ _ []

theorem trace_chain (caller : Label → Statement)
    (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (trace background flags memory word suffix target).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  apply PSTRWordBool.NativeTrace.join_chain _
    (configuration background flags (FieldCopy.copyPort word suffix target))
    [returned background flags word suffix target]
    (prefixTrace_last _ _ _ _ _ _) (prefixTrace_chain caller _ _ _ _ _ _)
  exact List.isChain_cons_cons.mpr
    ⟨return_edge caller _ _ _ _ _, List.isChain_singleton _⟩

theorem trace_length (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (trace background flags memory word suffix target).length = 2 * word.length + 4 := by
  simp only [trace, prefixTrace, List.length_append, List.length_map,
    FieldCopy.copyPortTrace_length, List.length_cons, List.length_nil]

theorem trace_transitions (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (trace background flags memory word suffix target).length - 1 = 2 * word.length + 3 := by
  rw [trace_length]
  omega

theorem trace_frames (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    ∀ current ∈ trace background flags memory word suffix target,
      current.var.2 = flags ∧
      ∀ point, (∀ slot, point ≠ role slot) → current.stk point = background point := by
  intro current present
  rcases List.mem_append.mp present with copied | port
  · obtain ⟨small, _, rfl⟩ := List.mem_map.mp copied
    exact ⟨rfl, fun point outside => stacks_frame _ _ point outside⟩
  · have same := List.mem_singleton.mp port
    subst current
    exact ⟨rfl, fun point outside => stacks_frame _ _ point outside⟩

theorem trace_mass (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    ∀ current ∈ trace background flags memory word suffix target,
      occupied current ≤ outsideOccupied background +
        3 * word.length + suffix.length + target.length := by
  intro current present
  rcases List.mem_append.mp present with copied | port
  · obtain ⟨small, member, rfl⟩ := List.mem_map.mp copied
    rw [occupied_configuration]
    have bound := FieldCopy.copyPortTrace_mass memory word suffix target small member
    omega
  · have same := List.mem_singleton.mp port
    subst current
    exact (returned_occupied background flags word suffix target).le

/-- A caller-linked execution with genuine return cost. The next caller
instruction at label 3 is not included, and no raw I/O claim is made. -/
theorem actual_copy_return (caller : Label → Statement)
    (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (trace background flags memory word suffix target).head? =
      some (configuration background flags (FieldCopy.copyStart memory word suffix target)) ∧
    (trace background flags memory word suffix target).IsChain
      (fun before after => TM2.step (program caller) before = some after) ∧
    (trace background flags memory word suffix target).getLast? =
      some (returned background flags word suffix target) ∧
    (returned background flags word suffix target).l = some 3 ∧
    (returned background flags word suffix target).stk 3 = word ++ suffix ∧
    (returned background flags word suffix target).stk 10 = word ++ target ∧
    (returned background flags word suffix target).stk 11 = List.replicate word.length true ∧
    (returned background flags word suffix target).stk 7 = [] ∧
    (returned background flags word suffix target).stk 12 = [] ∧
    (trace background flags memory word suffix target).length = 2 * word.length + 4 ∧
    (∀ current ∈ trace background flags memory word suffix target,
      current.var.2 = flags ∧
      ∀ point, (∀ slot, point ≠ role slot) → current.stk point = background point) ∧
    ∀ current ∈ trace background flags memory word suffix target,
      occupied current ≤ outsideOccupied background +
        3 * word.length + suffix.length + target.length :=
  ⟨trace_head _ _ _ _ _ _, trace_chain caller _ _ _ _ _ _, trace_last _ _ _ _ _ _,
    rfl, rfl, rfl, rfl, rfl, rfl, trace_length _ _ _ _ _ _,
    trace_frames _ _ _ _ _ _, trace_mass _ _ _ _ _ _⟩

end PaperProofs.Common.Native.PSTRWordVM.BankCopy
