module

public import Paid.PDROC_D27Prepare_Program_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.D27Prepare.Memory

open PaperProofs.Paid.Computation
open Program

/-- A typed physical slot in the proof memory matched to the actual heap. -/
def Has (memory : SlotMemory) (address : ℕ) (value : Cell) : Prop :=
  address ∈ memory.present ∧ memory.value address = value

theorem Has.write_same (memory : SlotMemory) (address : ℕ) (value : Cell) :
    Has (memory.write address value) address value := by
  simp [Has, SlotMemory.write]

theorem Has.write_other (memory : SlotMemory) (address target : ℕ) (value stored : Cell)
    (h : Has memory address value) (different : address ≠ target) :
    Has (memory.write target stored) address value := by
  constructor
  · exact Finset.mem_insert_of_mem h.1
  · simpa only [SlotMemory.write, Function.update_of_ne different] using h.2

theorem constant_eval (memory : SlotMemory) (target : ℕ) (value : Cell) :
    (SlotCommand.constant target value).eval memory = some (memory.write target value) := rfl

theorem copy_eval (memory : SlotMemory) (source target : ℕ) (value : Cell)
    (h : Has memory source value) :
    (SlotCommand.copy source target).eval memory = some (memory.write target value) := by
  simp only [SlotCommand.eval, h.1, ↓reduceIte, h.2]

theorem natural_eval (memory : SlotMemory) (operation : NatOp) (left right target x y result : ℕ)
    (hl : Has memory left (.natural x)) (hr : Has memory right (.natural y))
    (hop : operation.eval x y = some result) :
    (SlotCommand.natural operation left right target).eval memory =
      some (memory.write target (.natural result)) := by
  simp only [SlotCommand.eval, hl.1, hr.1, and_self, ↓reduceIte, hl.2, hr.2, Cell.nat?]
  change Option.bind (operation.eval x y)
    (fun value => some (memory.write target (.natural value))) = some (memory.write target (.natural result))
  simp only [hop, Option.bind_some]

theorem rational_eval (memory : SlotMemory) (operation : RatOp) (left right target : ℕ) (x y result : ℚ)
    (hl : Has memory left (.rational x)) (hr : Has memory right (.rational y))
    (hop : operation.eval x y = some result) :
    (SlotCommand.rational operation left right target).eval memory =
      some (memory.write target (.rational result)) := by
  simp only [SlotCommand.eval, hl.1, hr.1, and_self, ↓reduceIte, hl.2, hr.2, Cell.rat?]
  change Option.bind (operation.eval x y)
    (fun value => some (memory.write target (.rational value))) = some (memory.write target (.rational result))
  simp only [hop, Option.bind_some]

theorem cast_eval (memory : SlotMemory) (source target value : ℕ)
    (h : Has memory source (.natural value)) :
    (SlotCommand.toRational source target).eval memory =
      some (memory.write target (.rational value)) := by
  simp only [SlotCommand.eval, h.1, ↓reduceIte, h.2, Cell.nat?]
  rfl

theorem match_has (state : State) (memory : SlotMemory) (address : ℕ) (value : Cell)
    (matched : MemoryMatch state memory) (h : Has memory address value) :
    address ∈ state.live ∧ state.heap address = value := by
  simpa only [Has, matched.live, matched.heap] using h

theorem has_of_match (state : State) (memory : SlotMemory) (address : ℕ) (value : Cell)
    (matched : MemoryMatch state memory) (h : address ∈ state.live ∧ state.heap address = value) :
    Has memory address value := by
  simpa only [Has, matched.live, matched.heap] using h

theorem sequence_cons (first : SlotCommand) (rest : List SlotCommand)
    (before middle after : SlotMemory)
    (hfirst : first.eval before = some middle)
    (hrest : slotSequenceEval rest middle = some after) :
    slotSequenceEval (first :: rest) before = some after := by
  simpa only [slotSequenceEval, hfirst, Option.bind_some] using hrest

/-- This is the unique address that the literal macro can store to. -/
def target : SlotCommand → ℕ
  | .constant address _ => address
  | .copy _ address => address
  | .natural _ _ _ address => address
  | .rational _ _ _ address => address
  | .toRational _ address => address

theorem eval_is_write (command : SlotCommand) (memory next : SlotMemory)
    (executed : command.eval memory = some next) :
    ∃ value, next = memory.write (target command) value := by
  cases command with
  | constant address value =>
      exact ⟨value, (Option.some.inj executed).symm⟩
  | copy source address =>
      simp only [SlotCommand.eval] at executed
      split at executed
      · exact ⟨memory.value source, (Option.some.inj executed).symm⟩
      · cases executed
  | natural operation left right address =>
      simp only [SlotCommand.eval] at executed
      split at executed
      · obtain ⟨x, _, rest⟩ := Option.bind_eq_some_iff.mp executed
        obtain ⟨y, _, rest⟩ := Option.bind_eq_some_iff.mp rest
        obtain ⟨value, _, last⟩ := Option.bind_eq_some_iff.mp rest
        exact ⟨.natural value, (Option.some.inj last).symm⟩
      · cases executed
  | rational operation left right address =>
      simp only [SlotCommand.eval] at executed
      split at executed
      · obtain ⟨x, _, rest⟩ := Option.bind_eq_some_iff.mp executed
        obtain ⟨y, _, rest⟩ := Option.bind_eq_some_iff.mp rest
        obtain ⟨value, _, last⟩ := Option.bind_eq_some_iff.mp rest
        exact ⟨.rational value, (Option.some.inj last).symm⟩
      · cases executed
  | toRational source address =>
      simp only [SlotCommand.eval] at executed
      split at executed
      · obtain ⟨value, _, last⟩ := Option.bind_eq_some_iff.mp executed
        exact ⟨.rational value, (Option.some.inj last).symm⟩
      · cases executed

theorem sequence_preserves (commands : List SlotCommand) (memory next : SlotMemory)
    (executed : slotSequenceEval commands memory = some next)
    (address : ℕ) (value : Cell) (h : Has memory address value)
    (unwritten : ∀ command ∈ commands, address ≠ target command) : Has next address value := by
  induction commands generalizing memory with
  | nil =>
      have same : memory = next := Option.some.inj executed
      simpa only [same] using h
  | cons command rest ih =>
      obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp executed
      obtain ⟨stored, same⟩ := eval_is_write command memory middle first
      apply ih middle later
      · rw [same]
        exact Has.write_other memory address (target command) value stored h (unwritten command (by simp))
      · intro other member
        exact unwritten other (by simp only [List.mem_cons]; exact Or.inr member)

end PDROC.D27Prepare.Memory
