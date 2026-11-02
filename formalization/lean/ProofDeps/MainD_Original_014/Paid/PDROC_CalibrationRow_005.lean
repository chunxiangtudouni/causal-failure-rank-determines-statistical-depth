module

public import Paid.PDROC_CalibrationRow_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Memory frames for every successful actual literal prefix, including
the whole body. This will be attached to actual kernel trace witnesses. -/
def LinearFrames (region : Finset ℕ) (input : List Cell) (code : List Instruction) (before : State) : Prop :=
  ∀ count after,linearExecute input (code.take count) before=some after → MemoryFrame region before after

theorem LinearFrames.nil (region : Finset ℕ) (input : List Cell) (before : State) :
    LinearFrames region input [] before := by
  intro count after executed
  have same : before=after := Option.some.inj (by simpa only [List.take_nil,linearExecute] using executed)
  subst after
  exact MemoryFrame.refl region before

theorem LinearFrames.cons (region : Finset ℕ) (input : List Cell)
    (instruction : Instruction) (rest : List Instruction) (before middle : State)
    (executed : instruction.execute input before=some middle)
    (firstFrame : MemoryFrame region before middle)
    (laterFrames : LinearFrames region input rest middle) :
    LinearFrames region input (instruction::rest) before := by
  intro count after executedPrefix
  cases count with
  | zero =>
      have same : before=after := Option.some.inj executedPrefix
      subst after
      exact MemoryFrame.refl region before
  | succ count =>
      simp only [List.take_succ_cons,linearExecute,executed,Option.bind_some] at executedPrefix
      exact firstFrame.trans (laterFrames count after executedPrefix)

theorem LinearFrames.final {region : Finset ℕ} {input : List Cell} {code : List Instruction}
    {before after : State} (frames : LinearFrames region input code before)
    (executed : linearExecute input code before=some after) : MemoryFrame region before after := by
  apply frames code.length after
  simpa only [List.take_length] using executed

theorem LinearFrames.append (region : Finset ℕ) (input : List Cell) (first later : List Instruction)
    (before middle : State) (executed : linearExecute input first before=some middle)
    (firstFrames : LinearFrames region input first before)
    (laterFrames : LinearFrames region input later middle) :
    LinearFrames region input (first++later) before := by
  intro count after executedPrefix
  by_cases short : count ≤ first.length
  · rw [List.take_append_of_le_length short] at executedPrefix
    exact firstFrames count after executedPrefix
  · rw [List.take_append,List.take_of_length_le (by omega : first.length ≤ count),
      linearExecute_append,executed,Option.bind_some] at executedPrefix
    exact (firstFrames.final executed).trans (laterFrames (count-first.length) after executedPrefix)

/-- Static non-storing fragments are framed at every runtime state;
actual store fragments instead discharge their typed runtime address. -/
theorem linearExecute_frame_of_static (region : Finset ℕ) (input : List Cell) (code : List Instruction)
    (safe : ∀ instruction ∈ code,∀ state,WritesWithin region instruction state)
    (before after : State) (executed : linearExecute input code before=some after) :
    MemoryFrame region before after := by
  induction code generalizing before with
  | nil =>
      have same : before=after := Option.some.inj executed
      subst after
      exact MemoryFrame.refl region before
  | cons instruction rest ih =>
      obtain ⟨middle,first,later⟩ := Option.bind_eq_some_iff.mp executed
      have firstFrame := execute_memoryFrame region instruction input before middle
        (safe instruction (by simp) before) first
      exact firstFrame.trans (ih (fun next member => safe next (by simp only [List.mem_cons]; exact Or.inr member)) middle later)

theorem LinearFrames.of_static (region : Finset ℕ) (input : List Cell) (code : List Instruction)
    (safe : ∀ instruction ∈ code,∀ state,WritesWithin region instruction state) (before : State) :
    LinearFrames region input code before := by
  intro count after executed
  exact linearExecute_frame_of_static region input (code.take count)
    (fun instruction member => safe instruction (List.mem_of_mem_take member)) before after executed

theorem LinearFrames.store (region : Finset ℕ) (input : List Cell) (before : State)
    (source : Register) (address : ℕ) (pointer : before.register .address=.natural address)
    (inside : address ∈ region) : LinearFrames region input [.store .address source] before := by
  let after : State :=
    {before with
      heap:=Function.update before.heap address (before.register source)
      live:=insert address before.live
      pc:=before.pc+1}
  have executed : (Instruction.store .address source).execute input before=some after :=
    execute_store .address source input before address pointer
  have safe : WritesWithin region (.store .address source) before := by
    intro actual fetched
    have same : address=actual := by simpa only [pointer,Cell.nat?,Option.some.injEq] using fetched
    simpa only [←same] using inside
  apply LinearFrames.cons region input (.store .address source) [] before after executed
    (execute_memoryFrame region _ input before after safe executed)
  exact LinearFrames.nil region input after

end PDROC.CalibrationRow
