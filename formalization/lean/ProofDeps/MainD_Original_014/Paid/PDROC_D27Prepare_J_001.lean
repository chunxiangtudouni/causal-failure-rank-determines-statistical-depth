module

public import Paid.PDROC_D27Prepare_Q_008
public import Paid.PDROC_D27Prepare_Search_005
public import Paid.PDROC_D27Prepare_Resources_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.J

/-- Generic actual bounded command page, with an explicit region rather
than the Q-specific region. This is used by the original tail/J phases.
Semantic commands are proof certificates for the literal ISA program. -/
theorem sequence_page_segment (R : Finset ℕ) (input : List Cell) (B page target : ℕ)
    (inside : page < pageCount) (commands : List SlotCommand)
    (layout : pageCode page = slotSequenceCode commands ++ go target)
    (before : State) (location : before.pc = pc page) (memory next : SlotMemory)
    (matched : MemoryMatch before memory) (evaluated : slotSequenceEval commands memory = some next)
    (bounded : StateBounds 64 B before) (semantic : SequenceMemoryBounds commands memory 64 B)
    (addressBits : 1 + natBits 64 ≤ B)
    (addresses : ∀ command ∈ commands, CommandAddresses 64 command)
    (writes : ∀ command ∈ commands, Memory.target command ∈ R) :
    ∃ after : State, MemoryMatch after next ∧ after.pc = pc target ∧
      Segment R input before after 64 B ((slotSequenceCode commands).length + 2) := by
  obtain ⟨after, trace, afterMatch, afterPc, output, head, last, length, chain, members,
    terminal, executed, afterShape⟩ :=
    Search.sequence_page_trace input page target inside commands layout before location memory next matched evaluated
  have bits := slotSequence_prefix_bounds commands input before memory next 64 B
    matched bounded addresses addressBits evaluated semantic
  have frames := sequence_prefix_memory R commands input before memory next matched evaluated writes
  refine ⟨after, afterMatch, afterPc, ⟨⟨trace, head, last, chain, length.le, ?_, ?_⟩,
    output, afterMatch.base.trans matched.base.symm⟩⟩
  · exact page_trace_bounds input _ before terminal after (pc target) 64 B
      trace bits executed afterShape members
  · intro state member
    rcases members state member with same | ⟨count, _, actual⟩
    · subst state
      rw [afterShape]
      exact (frames.final executed).with_pc (pc target)
    · exact frames count state actual

end PDROC.D27Prepare.J
