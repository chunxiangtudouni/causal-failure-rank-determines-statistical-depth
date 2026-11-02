module

public import Paid.PDMenu_ComputeFrame_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation

/-- Memory-only frame on an arbitrary finite runtime workspace. -/
def MemoryFrame (region : Finset ℕ) (before after : State) : Prop :=
  (∀ address ∉ region, after.heap address=before.heap address) ∧
    (∀ address ∉ region, address ∈ after.live ↔ address ∈ before.live)

def WritesWithin (region : Finset ℕ) (instruction : Instruction) (before : State) : Prop :=
  match instruction with
  | .store pointer _ | .release pointer =>
    ∀ address, (before.register pointer).nat?=some address → address ∈ region
  | _ => True

def NoOutputInstruction : Instruction → Prop
  | .output _ => False
  | _ => True

theorem MemoryFrame.refl (region : Finset ℕ) (state : State) : MemoryFrame region state state :=
  ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩

theorem MemoryFrame.trans {region : Finset ℕ} {before middle after : State}
    (first : MemoryFrame region before middle) (later : MemoryFrame region middle after) : MemoryFrame region before after :=
  ⟨fun a h => (later.1 a h).trans (first.1 a h),fun a h => (later.2 a h).trans (first.2 a h)⟩

private theorem memoryFrame_store (region : Finset ℕ) (before : State) (address : ℕ) (value : Cell)
    (inside : address ∈ region) :
    MemoryFrame region before
      {before with
        heap:=Function.update before.heap address value
        live:=insert address before.live
        pc:=before.pc+1} := by
  have different (query : ℕ) (outside : query ∉ region) : query ≠ address := by
    intro eq
    exact outside (eq.symm ▸ inside)
  constructor
  · intro query outside
    exact Function.update_of_ne (different query outside) _ _
  · intro query outside
    simp only [Finset.mem_insert,different query outside,false_or]

private theorem memoryFrame_release (region : Finset ℕ) (before : State) (address : ℕ)
    (inside : address ∈ region) :
    MemoryFrame region before
      {before with
        heap:=Function.update before.heap address (.natural 0)
        live:=before.live.erase address
        pc:=before.pc+1} := by
  have different (query : ℕ) (outside : query ∉ region) : query ≠ address := by
    intro eq
    exact outside (eq.symm ▸ inside)
  constructor
  · intro query outside
    exact Function.update_of_ne (different query outside) _ _
  · intro query outside
    rw [Finset.mem_erase]
    exact ⟨fun h => h.2,fun h => ⟨different query outside,h⟩⟩

/-- Actual success of every ORIGINAL ISA constructor is inspected. Only
the real store/release address needs membership in the workspace; no
static label or final memory summary substitutes for this per-step fact. -/
theorem execute_memoryFrame (region : Finset ℕ) (instruction : Instruction)
    (input : List Cell) (before after : State) (safe : WritesWithin region instruction before)
    (run : instruction.execute input before=some after) : MemoryFrame region before after := by
  cases instruction
  case store pointer source =>
    obtain ⟨address,haddress,he⟩ := Option.bind_eq_some_iff.mp run
    have heq := Option.some.inj he
    subst after
    exact memoryFrame_store region before address (before.register source) (safe address haddress)
  case release pointer =>
    obtain ⟨address,haddress,he⟩ := Option.bind_eq_some_iff.mp run
    have heq := Option.some.inj he
    subst after
    exact memoryFrame_release region before address (safe address haddress)
  all_goals simp_all [WritesWithin,Instruction.execute,State.set,Option.bind_eq_some_iff]
  all_goals repeat' (obtain ⟨argument,equation,run⟩ := run)
  all_goals simp_all [MemoryFrame]

theorem execute_output_eq_of_noOutput (instruction : Instruction) (input : List Cell) (before after : State)
    (safe : NoOutputInstruction instruction) (run : instruction.execute input before=some after) :
    after.output=before.output := by
  cases instruction <;> simp_all [NoOutputInstruction,Instruction.execute,State.set,Option.bind_eq_some_iff]
  all_goals repeat' (obtain ⟨argument,equation,run⟩ := run)
  all_goals simp_all

theorem execute_output_length_le (instruction : Instruction) (input : List Cell) (before after : State)
    (run : instruction.execute input before=some after) : after.output.length ≤ before.output.length+1 := by
  cases instruction <;> simp_all [Instruction.execute,State.set,Option.bind_eq_some_iff]
  all_goals repeat' (obtain ⟨argument,equation,run⟩ := run)
  all_goals simp_all

end PDMenu.ComputeFrame
