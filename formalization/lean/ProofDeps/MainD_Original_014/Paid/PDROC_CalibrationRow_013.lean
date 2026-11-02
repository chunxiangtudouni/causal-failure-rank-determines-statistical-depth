module

public import Paid.PDROC_CalibrationRow_003
public import Paid.PDROC_CalibrationRow_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

def noRelease : Instruction → Bool
  | .release _ => false
  | _ => true

theorem execute_live_mono (instruction : Instruction) (input : List Cell) (before after : State)
    (safe : noRelease instruction=true) (run : instruction.execute input before=some after) :
    before.live ⊆ after.live := by
  cases instruction
  case store pointer source =>
    obtain ⟨address,_,executed⟩ := Option.bind_eq_some_iff.mp run
    have equal := Option.some.inj executed
    subst after
    exact Finset.subset_insert _ _
  all_goals simp_all [noRelease,Instruction.execute,State.set,Option.bind_eq_some_iff]
  all_goals repeat' (obtain ⟨argument,equation,run⟩ := run)
  all_goals simp_all

theorem linearExecute_live_mono (input : List Cell) (code : List Instruction)
    (safe : ∀ instruction ∈ code,noRelease instruction=true) (before after : State)
    (run : linearExecute input code before=some after) : before.live ⊆ after.live := by
  induction code generalizing before with
  | nil =>
    have equal := Option.some.inj run
    subst after
    exact fun _ member => member
  | cons instruction rest ih =>
    obtain ⟨middle,first,later⟩ := Option.bind_eq_some_iff.mp run
    exact (execute_live_mono instruction input before middle (safe instruction (by simp)) first).trans
      (ih (fun next member => safe next (by simp only [List.mem_cons]; exact Or.inr member)) middle later)

theorem rowBody_noRelease (label : Label) (_inside : rowLabel label=true) :
    ∀ instruction ∈ (basicBlock label).body,noRelease instruction=true := by
  have all : (basicBlock label).body.all noRelease=true := by
    cases label <;> rfl
  exact List.all_eq_true.mp all

/-- Every real row-block prefix retains all allocated header words.
This includes the scratch header words inside the mutable row region. -/
theorem rowBody_prefix_live (input : List Cell) (label : Label) (inside : rowLabel label=true)
    (before state : State) (count : ℕ)
    (run : linearExecute input ((basicBlock label).body.take count) before=some state) :
    before.live ⊆ state.live :=
  linearExecute_live_mono input _
    (fun instruction member => rowBody_noRelease label inside instruction (List.mem_of_mem_take member))
    before state run

/-- The actual instruction-prefix witness is kept, rather than merely
a final RowAt and a final frame. Runtime phase certificates specialize
these very prefix states to the real clock/cursor/read/scatter formulas. -/
theorem row_block_prefix_trace (origin : ℕ) (input : List Cell) (label : Label)
    (before middle after : State) (position : before.pc=labelAddress origin label)
    (body : linearExecute input (basicBlock label).body before=some middle)
    (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.length=(basicBlock label).body.length+2 ∧
      trace.IsChain (fun a b => step (locatedBlock origin (kernel origin)) input a=some b) ∧
      time (locatedBlock origin (kernel origin)) trace ≤ 15*((basicBlock label).body.length+2) ∧
      ∀ state ∈ trace,
        (∃ count ≤ (basicBlock label).body.length,
          linearExecute input ((basicBlock label).body.take count) before=some state) ∨ state=after := by
  obtain ⟨first,head,last,length,chain,middlePc,_,strict⟩ :=
    kernel_body_trace origin label input before middle position body
  have actual : step (locatedBlock origin (kernel origin)) input middle=some after := by
    rw [kernel_control_step origin label input middle middlePc]
    exact control
  have wholeChain := (chain_append_control (locatedBlock origin (kernel origin)) input first middle after chain last actual).1
  have wholeLength : (first++[after]).length=(basicBlock label).body.length+2 := by
    simp only [List.length_append,List.length_singleton,length,Nat.add_assoc]
  refine ⟨first++[after],?_,by simp,wholeLength,wholeChain,?_,?_⟩
  · cases first with
    | nil => simp at head
    | cons start rest => exact head
  · simpa only [wholeLength] using time_le_length (locatedBlock origin (kernel origin)) (first++[after])
  · have split : first.dropLast++[middle]=first := List.dropLast_append_getLast? middle (by rw [last]; simp)
    intro state member
    rcases List.mem_append.mp member with early|late
    · left
      rw [←split,List.mem_append,List.mem_singleton] at early
      rcases early with proper|equal
      · obtain ⟨count,bound,run⟩ := strict state proper
        exact ⟨count,Nat.le_of_lt bound,run⟩
      · subst state
        exact ⟨_,Nat.le_refl _,by simpa only [List.take_length] using body⟩
    · exact Or.inr (List.mem_singleton.mp late)

end PDROC.CalibrationRow
