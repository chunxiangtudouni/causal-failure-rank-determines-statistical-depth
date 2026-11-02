module

public import Paid.PDROC_D27Prepare_Resources_005
public import Paid.PDROC_D27Prepare_Program_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute
open PDROC.D27Prepare.Program

namespace PDROC.D27Prepare.Resources

structure MemoryBounds (H B : ℕ) (memory : SlotMemory) : Prop where
  present : memory.present ⊆ Finset.range H
  values : ∀ address ∈ memory.present, (memory.value address).bits ≤ B

theorem MemoryBounds.write {H B : ℕ} {memory : SlotMemory} (h : MemoryBounds H B memory)
    (target : ℕ) (value : Cell) (inside : target < H) (bits : value.bits ≤ B) :
    MemoryBounds H B (memory.write target value) := by
  constructor
  · intro address member
    rcases Finset.mem_insert.mp member with same | old
    · subst address
      exact Finset.mem_range.mpr inside
    · exact h.present old
  · intro address member
    by_cases same : address = target
    · subst address
      simpa [SlotMemory.write] using bits
    · have old := (Finset.mem_insert.mp member).resolve_left same
      simpa [SlotMemory.write, same] using h.values address old

def CommandAddresses (H : ℕ) : SlotCommand → Prop
  | .constant target _ => target < H
  | .copy source target => source < H ∧ target < H
  | .natural _ left right target => left < H ∧ right < H ∧ target < H
  | .rational _ left right target => left < H ∧ right < H ∧ target < H
  | .toRational source target => source < H ∧ target < H

/-- A semantic command's bounded stored cell suffices for all its actual
literal prefixes. Every macro read occurs before its write, so aliasing
does not require a disjointness premise. -/
theorem command_prefix_bounds (command : SlotCommand) (input : List Cell) (before : State)
    (memory next : SlotMemory) (H B : ℕ) (matched : MemoryMatch before memory)
    (hbefore : StateBounds H B before) (addresses : CommandAddresses H command)
    (addressBits : 1 + natBits H ≤ B) (heval : command.eval memory = some next)
    (hnext : MemoryBounds H B next) :
    LinearPrefixBounds input command.code before H B := by
  cases command with
  | constant target value =>
      have same : memory.write target value = next := Option.some.inj heval
      subst next
      apply constantSlot_prefix_bounds input before target H B value hbefore matched.base addresses addressBits
      simpa [SlotMemory.write] using hnext.values target (by simp [SlotMemory.write])
  | copy source target =>
      have hs : source ∈ memory.present := by
        by_contra hn
        simp [SlotCommand.eval, hn] at heval
      exact copySlot_prefix_bounds input before source target H B hbefore matched.base
        (by simpa only [matched.live] using hs) addresses.1 addresses.2 addressBits
  | natural operation left right target =>
      have hs : left ∈ memory.present ∧ right ∈ memory.present := by
        by_contra hn
        simp [SlotCommand.eval, hn] at heval
      cases hx : memory.value left with
      | rational x => simp [SlotCommand.eval, hs, hx, Cell.nat?] at heval
      | natural x =>
          cases hy : memory.value right with
          | rational y => simp [SlotCommand.eval, hs, hx, hy, Cell.nat?] at heval
          | natural y =>
              have he : ((operation.eval x y).bind fun value => some (memory.write target (.natural value))) = some next := by
                simpa [SlotCommand.eval, hs, hx, hy, Cell.nat?] using heval
              obtain ⟨value, hop, hn⟩ := Option.bind_eq_some_iff.mp he
              have same : memory.write target (.natural value) = next := Option.some.inj hn
              subst next
              apply natBinarySlots_prefix_bounds input before left right target H B operation x y value
                hbefore matched.base (by simpa only [matched.live] using hs.1)
                (by simpa only [matched.live] using hs.2)
                (by simpa only [matched.heap] using hx) (by simpa only [matched.heap] using hy)
                addresses.1 addresses.2.1 addresses.2.2 addressBits _ hop
              simpa [SlotMemory.write] using hnext.values target (by simp [SlotMemory.write])
  | rational operation left right target =>
      have hs : left ∈ memory.present ∧ right ∈ memory.present := by
        by_contra hn
        simp [SlotCommand.eval, hn] at heval
      cases hx : memory.value left with
      | natural x => simp [SlotCommand.eval, hs, hx, Cell.rat?] at heval
      | rational x =>
          cases hy : memory.value right with
          | natural y => simp [SlotCommand.eval, hs, hx, hy, Cell.rat?] at heval
          | rational y =>
              have he : ((operation.eval x y).bind fun value => some (memory.write target (.rational value))) = some next := by
                simpa [SlotCommand.eval, hs, hx, hy, Cell.rat?] using heval
              obtain ⟨value, hop, hn⟩ := Option.bind_eq_some_iff.mp he
              have same : memory.write target (.rational value) = next := Option.some.inj hn
              subst next
              apply ratBinarySlots_prefix_bounds input before left right target H B operation x y value
                hbefore matched.base (by simpa only [matched.live] using hs.1)
                (by simpa only [matched.live] using hs.2)
                (by simpa only [matched.heap] using hx) (by simpa only [matched.heap] using hy)
                addresses.1 addresses.2.1 addresses.2.2 addressBits _ hop
              simpa [SlotMemory.write] using hnext.values target (by simp [SlotMemory.write])
  | toRational source target =>
      have hs : source ∈ memory.present := by
        by_contra hn
        simp [SlotCommand.eval, hn] at heval
      cases hx : memory.value source with
      | rational x => simp [SlotCommand.eval, hs, hx, Cell.nat?] at heval
      | natural value =>
          have same : memory.write target (.rational value) = next := by
            simpa [SlotCommand.eval, hs, hx, Cell.nat?] using heval
          subst next
          apply natToRatSlot_prefix_bounds input before source target H B value hbefore matched.base
            (by simpa only [matched.live] using hs) (by simpa only [matched.heap] using hx)
            addresses.1 addresses.2 addressBits
          simpa [SlotMemory.write] using hnext.values target (by simp [SlotMemory.write])

/-- This condition is checked on the finitely many semantic commands in
a phase, not on a data-dependent host execution or desired whole output. -/
def SequenceMemoryBounds (commands : List SlotCommand) (memory : SlotMemory) (H B : ℕ) : Prop :=
  ∀ count next, slotSequenceEval (commands.take count) memory = some next → MemoryBounds H B next

theorem SequenceMemoryBounds.nil (memory : SlotMemory) (H B : ℕ)
    (bounded : MemoryBounds H B memory) : SequenceMemoryBounds [] memory H B := by
  intro count next executed
  have same : memory = next := Option.some.inj (by simpa only [List.take_nil, slotSequenceEval] using executed)
  subst next
  exact bounded

theorem SequenceMemoryBounds.cons (command : SlotCommand) (rest : List SlotCommand)
    (memory middle : SlotMemory) (H B : ℕ) (bounded : MemoryBounds H B memory)
    (executed : command.eval memory = some middle)
    (later : SequenceMemoryBounds rest middle H B) :
    SequenceMemoryBounds (command :: rest) memory H B := by
  intro count next heval
  cases count with
  | zero =>
      have same : memory = next := Option.some.inj (by simpa only [List.take_zero, slotSequenceEval] using heval)
      subst next
      exact bounded
  | succ count =>
      simp only [List.take_succ_cons, slotSequenceEval, executed, Option.bind_some] at heval
      exact later count next heval

theorem slotSequence_prefix_bounds (commands : List SlotCommand) (input : List Cell) (before : State)
    (memory next : SlotMemory) (H B : ℕ) (matched : MemoryMatch before memory)
    (hbefore : StateBounds H B before)
    (addresses : ∀ command ∈ commands, CommandAddresses H command)
    (addressBits : 1 + natBits H ≤ B) (heval : slotSequenceEval commands memory = some next)
    (semantic : SequenceMemoryBounds commands memory H B) :
    LinearPrefixBounds input (slotSequenceCode commands) before H B := by
  induction commands generalizing before memory with
  | nil => exact LinearPrefixBounds.nil input hbefore
  | cons command rest ih =>
      obtain ⟨middleMemory, firstEval, restEval⟩ := Option.bind_eq_some_iff.mp heval
      have firstMemoryBounds : MemoryBounds H B middleMemory := by
        apply semantic 1 middleMemory
        simp only [List.take_succ_cons, List.take_zero, slotSequenceEval, firstEval, Option.bind_some]
      have firstPrefix := command_prefix_bounds command input before memory middleMemory H B
        matched hbefore (addresses command (by simp)) addressBits firstEval firstMemoryBounds
      obtain ⟨middle, firstExecute, middleMatch, _, _⟩ :=
        command.realize input before memory middleMemory matched firstEval
      have middleBounds := firstPrefix.final firstExecute
      have restSemantic : SequenceMemoryBounds rest middleMemory H B := by
        intro count later laterEval
        apply semantic (count + 1) later
        simpa only [List.take_succ_cons, slotSequenceEval, firstEval, Option.bind_some] using laterEval
      have restAddresses : ∀ other ∈ rest, CommandAddresses H other := by
        intro other member
        exact addresses other (by simp only [List.mem_cons]; exact Or.inr member)
      have restPrefix := ih middle middleMemory middleMatch middleBounds restAddresses restEval restSemantic
      simpa only [slotSequenceCode, List.flatMap_cons] using
        LinearPrefixBounds.append input command.code (slotSequenceCode rest) before middle H B
          firstExecute firstPrefix restPrefix

end PDROC.D27Prepare.Resources
