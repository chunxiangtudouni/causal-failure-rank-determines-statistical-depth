module

public import Paid.PDROC_CalibrationRow_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

def rowLabel : Label → Bool
  | .levelInit | .initGate | .initCell | .initCenter | .initStore | .stepStart | .stepGate |
      .zeroStart | .zeroGate | .zeroCell | .scatterStart | .scatterGate |
      .leftRead | .leftInterior | .leftStore | .rightRead | .rightInterior | .rightStore |
      .scatterNext | .stepNext => true
  | _ => false

def noOutput : Instruction → Bool
  | .output _ => false
  | _ => true

theorem noOutput_correct (instruction : Instruction) :
    noOutput instruction=true ↔ NoOutputInstruction instruction := by
  cases instruction <;> simp [noOutput,NoOutputInstruction]

theorem rowBody_noOutput (label : Label) (inside : rowLabel label=true) :
    ∀ instruction ∈ (basicBlock label).body, NoOutputInstruction instruction := by
  have all : (basicBlock label).body.all noOutput=true := by
    cases label <;> first | rfl | cases inside
  intro instruction member
  exact (noOutput_correct instruction).mp ((List.all_eq_true.mp all) instruction member)

theorem linearExecute_noOutput (input : List Cell) (code : List Instruction)
    (safe : ∀ instruction ∈ code, NoOutputInstruction instruction) (before after : State)
    (run : linearExecute input code before=some after) : after.output=before.output := by
  induction code generalizing before with
  | nil =>
      have same : before=after := Option.some.inj run
      subst after
      rfl
  | cons instruction rest ih =>
      obtain ⟨middle,first,later⟩ := Option.bind_eq_some_iff.mp run
      exact (ih (fun next member => safe next (by simp only [List.mem_cons]; exact Or.inr member))
        middle later).trans (execute_output_eq_of_noOutput instruction input before middle
          (safe instruction (by simp)) first)

theorem rowBody_prefix_output (input : List Cell) (label : Label) (inside : rowLabel label=true)
    (before state : State) (count : ℕ)
    (run : linearExecute input ((basicBlock label).body.take count) before=some state) :
    state.output=before.output :=
  linearExecute_noOutput input _
    (fun instruction member => rowBody_noOutput label inside instruction (List.mem_of_mem_take member))
    before state run

theorem rowBody_prefix_fresh (input : List Cell) (label : Label)
    (before state : State) (count : ℕ)
    (run : linearExecute input ((basicBlock label).body.take count) before=some state) :
    state.register .fresh=before.register .fresh :=
  linearExecute_preserves_fresh input _
    (fun instruction member => basicBlock_noFresh label instruction (List.mem_of_mem_take member))
    before state run

theorem control_noFresh (origin : ℕ) (control : Control) :
    noFresh (controlInstruction origin control)=true := by cases control <;> rfl

theorem control_noOutput (origin : ℕ) (control : Control) :
    NoOutputInstruction (controlInstruction origin control) := by cases control <;> trivial

/-- Genuine block trace foundation, exposing all actual prefix states.
Local loop theorems must still establish the literal body/control success. -/
theorem row_block_trace (origin : ℕ) (input : List Cell) (label : Label)
    (inside : rowLabel label=true) (before middle after : State)
    (position : before.pc=labelAddress origin label)
    (body : linearExecute input (basicBlock label).body before=some middle)
    (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.length=(basicBlock label).body.length+2 ∧
      trace.IsChain (fun a b => step (locatedBlock origin (kernel origin)) input a=some b) ∧
      time (locatedBlock origin (kernel origin)) trace ≤ 15*((basicBlock label).body.length+2) ∧
      ∀ state ∈ trace, state.output=before.output ∧ state.register .fresh=before.register .fresh := by
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
  · have middleOutput := linearExecute_noOutput input _ (rowBody_noOutput label inside) before middle body
    have middleFresh := kernel_body_preserves_fresh input label before middle body
    have afterOutput := execute_output_eq_of_noOutput _ input middle after
      (control_noOutput origin (basicBlock label).control) control
    have afterFresh := execute_preserves_fresh _ (control_noFresh origin (basicBlock label).control)
      input middle after control
    have split : first.dropLast++[middle]=first := List.dropLast_append_getLast? middle (by rw [last]; simp)
    intro state member
    rcases List.mem_append.mp member with early|late
    · rw [←split,List.mem_append,List.mem_singleton] at early
      rcases early with proper|equal
      · obtain ⟨count,_,run⟩ := strict state proper
        exact ⟨rowBody_prefix_output input label inside before state count run,
          rowBody_prefix_fresh input label before state count run⟩
      · subst state
        exact ⟨middleOutput,middleFresh⟩
    · have equal : state=after := List.mem_singleton.mp late
      subst state
      exact ⟨afterOutput.trans middleOutput,afterFresh.trans middleFresh⟩

end PDROC.CalibrationRow
