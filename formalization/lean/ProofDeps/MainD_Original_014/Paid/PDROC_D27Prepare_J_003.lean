module

public import Paid.PDROC_D27Prepare_J_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.J

theorem copy_page_segment (R : Finset ℕ) (input : List Cell) (B page join source target : ℕ)
    (inside : page < pageCount)
    (layout : pageCode page = slotSequenceCode [.copy source target] ++ go join)
    (sourceInside : source < 64) (targetInside : target < 64) (writes : target ∈ R)
    (before : State) (location : before.pc = pc page) (fresh : before.register .fresh = .natural 0)
    (value : Cell) (stored : Search.SlotHas before source value)
    (bounded : StateBounds 64 B before) (addressBits : 1 + natBits 64 ≤ B) :
    ∃ after : State, after.pc = pc join ∧ Search.SlotHas after target value ∧
      Segment R input before after 64 B 8 := by
  let memory : SlotMemory := ⟨before.heap, before.live⟩
  let next := memory.write target value
  have matched : MemoryMatch before memory := ⟨rfl, rfl, fresh⟩
  have command : (SlotCommand.copy source target).eval memory = some next :=
    copy_eval memory source target value stored
  have evaluated : slotSequenceEval [.copy source target] memory = some next := by
    simp only [slotSequenceEval, command, Option.bind_some]
  have memoryBound : MemoryBounds 64 B memory := ⟨bounded.live, bounded.heapValues⟩
  have valueBits : value.bits ≤ B := by simpa only [stored.2] using bounded.heapValues source stored.1
  have nextBound := memoryBound.write target value targetInside valueBits
  have semantic : SequenceMemoryBounds [.copy source target] memory 64 B :=
    SequenceMemoryBounds.cons _ [] memory next 64 B memoryBound command (SequenceMemoryBounds.nil next 64 B nextBound)
  have addresses : ∀ c ∈ [.copy source target], CommandAddresses 64 c := by
    intro c member
    have same := List.mem_singleton.mp member
    subst c
    exact ⟨sourceInside, targetInside⟩
  have targets : ∀ c ∈ [.copy source target], Memory.target c ∈ R := by
    intro c member
    have same := List.mem_singleton.mp member
    subst c
    exact writes
  obtain ⟨after, afterMatch, afterPc, segment⟩ := sequence_page_segment R input B page join inside
    [.copy source target] layout before location memory next matched evaluated bounded semantic addressBits addresses targets
  have actual := match_has after next target value afterMatch (Has.write_same memory target value)
  exact ⟨after, afterPc, actual, segment⟩

end PDROC.D27Prepare.J
