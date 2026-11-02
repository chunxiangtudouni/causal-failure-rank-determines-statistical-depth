module

public import Paid.PDROC_D27Prepare_Q_003
public import Paid.PDROC_D27Prepare_Search_005
public import Paid.PDROC_D27Prepare_Resources_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Q

theorem sequence_page_resources (P : Parameters) (fee : ℚ) (input : List Cell)
    (page target : ℕ) (inside : page < pageCount) (commands : List SlotCommand)
    (layout : pageCode page = slotSequenceCode commands ++ go target)
    (before : State) (location : before.pc = pc page) (memory next : SlotMemory)
    (matched : MemoryMatch before memory) (evaluated : slotSequenceEval commands memory = some next)
    (bounded : StateBounds 64 (operandBudget P fee) before)
    (semantic : SequenceMemoryBounds commands memory 64 (operandBudget P fee))
    (addresses : ∀ command ∈ commands, CommandAddresses 64 command)
    (writes : ∀ command ∈ commands, Memory.target command ∈ region) :
    ∃ (after : State) (trace : List State), MemoryMatch after next ∧ after.pc = pc target ∧
      after.output = before.output ∧ after.register .fresh = before.register .fresh ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length = (slotSequenceCode commands).length + 2 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      (∀ state ∈ trace, MemoryProgress region before state) := by
  obtain ⟨after, trace, afterMatch, afterPc, afterOutput, head, last, length, chain, members,
      terminal, executed, afterEq⟩ :=
    Search.sequence_page_trace input page target inside commands layout before location memory next matched evaluated
  have prefixBits := slotSequence_prefix_bounds commands input before memory next 64 (operandBudget P fee)
    matched bounded addresses (operandBudget_address_bits P fee) evaluated semantic
  have prefixMemory := sequence_prefix_memory region commands input before memory next matched evaluated writes
  refine ⟨after, trace, afterMatch, afterPc, afterOutput, afterMatch.base.trans matched.base.symm,
    head, last, length, chain, ?_, ?_⟩
  · exact page_trace_bounds input _ before terminal after (pc target) 64 (operandBudget P fee)
      trace prefixBits executed afterEq members
  · intro state member
    rcases members state member with same | early
    · subst state
      rw [afterEq]
      exact (prefixMemory.final executed).with_pc (pc target)
    · obtain ⟨count, _, actual⟩ := early
      exact prefixMemory count state actual

theorem progress_slot (before after : State) (frame : MemoryProgress region before after)
    (address : ℕ) (outside : address ∉ region) (value : Cell)
    (old : Search.SlotHas before address value) : Search.SlotHas after address value :=
  ⟨(frame.1.2 address outside).mpr old.1, (frame.1.1 address outside).trans old.2⟩

theorem progress_raw (P : Parameters) (fee : ℚ) (before after : State)
    (raw : Search.RawConstants P fee before) (frame : MemoryProgress region before after)
    (fresh : after.register .fresh = before.register .fresh) : Search.RawConstants P fee after := by
  apply Search.RawConstants.transport P fee before after raw _ frame.2 fresh
  intro address read
  apply frame.1.1 address
  intro member
  simp only [region, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl <;> omega

theorem finish_of_progress (P : Parameters) (fee : ℚ) (before after : State)
    (initial : QInitial P fee before) (frame : MemoryProgress region before after)
    (location : after.pc = pc 21) (fresh : after.register .fresh = before.register .fresh)
    (result : Search.SlotHas after 9 (.natural P.certificate.Q)) : Search.SearchFinished P fee after := by
  exact ⟨progress_raw P fee before after initial.raw frame fresh, location,
    progress_slot before after frame 6 (by decide) _ initial.t0,
    progress_slot before after frame 7 (by decide) _ initial.M,
    progress_slot before after frame 8 (by decide) _ initial.E, result,
    progress_slot before after frame 22 (by decide) _ initial.ratStages,
    progress_slot before after frame 23 (by decide) _ initial.ratT0,
    progress_slot before after frame 24 (by decide) _ initial.gammaSquared,
    progress_slot before after frame 25 (by decide) _ initial.variance,
    progress_slot before after frame 26 (by decide) _ initial.varianceSquared,
    progress_slot before after frame 27 (by decide) _ initial.majorityThreshold,
    progress_slot before after frame 29 (by decide) _ initial.menuRatio,
    progress_slot before after frame 30 (by decide) _ initial.odds,
    progress_slot before after frame 31 (by decide) _ initial.exponentThreshold⟩

end PDROC.D27Prepare.Q
