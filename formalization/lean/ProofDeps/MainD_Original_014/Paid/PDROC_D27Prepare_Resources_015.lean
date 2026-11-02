module

public import Paid.PDROC_D27Prepare_Resources_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDROC.D27Prepare.Program PDMenu.ComputeFrame

namespace PDROC.D27Prepare.Resources

/-- A genuine fixed-program input trace with every intermediate register
and live heap cell bounded. Only the six raw cell bounds are premises. -/
theorem bounded_prologue_trace (c0 c1 c2 c3 c4 c5 : Cell) (B : ℕ)
    (enough : 8≤B) (inputBits : ∀ cell ∈ sixInput c0 c1 c2 c3 c4 c5,cell.bits≤B) :
    ∃ (after : State) (trace : List State),
      MemoryMatch after (initializedInputMemory c0 c1 c2 c3 c4 c5) ∧
      after.pc=pc 1 ∧ after.output=[] ∧ trace.head?=some initial ∧
      trace.getLast?=some after ∧ trace.length=89 ∧
      trace.IsChain (fun first later => step program (sixInput c0 c1 c2 c3 c4 c5) first=some later) ∧
      time program trace≤15*89 ∧ ∀ state∈trace,StateBounds 64 B state := by
  let input := sixInput c0 c1 c2 c3 c4 c5
  obtain ⟨middle,bodyExecute,middleMatch,middlePc,middleOutput⟩ := prologue_body_realize c0 c1 c2 c3 c4 c5
  have prefixBounds := prologue_prefix_bounds c0 c1 c2 c3 c4 c5 B enough inputBits
  have bodyFetch : FetchesCode program initial.pc prologueBody := by
    have h := fetches_page_part 0 (by decide) [] prologueBody (go 1)
      (by simpa only [pageCode,List.nil_append] using prologue_decompose)
    simpa [initial,pc] using h
  have jumpFetch : program[middle.pc]?=some (.jump (pc 1)) := by
    rw [middlePc]
    have h := fetches_page 0 (by decide) 87 (by decide)
    change program[87]?=some (.jump (pc 1)) at h
    exact h
  let after : State := {middle with pc:=pc 1}
  have afterBounds : StateBounds 64 B after := (prefixBounds.final bodyExecute).with_pc (pc 1)
  obtain ⟨body,trace,_,_,bodyLast,_,_,bodyStrict,wholeHead,wholeLast,wholeLength,wholeChain,wholeTime,wholeMembers⟩ :=
    literal_control_trace input prologueBody prologueBody_straight initial middle after bodyFetch bodyExecute
      (jump_step input middle (pc 1) jumpFetch)
  refine ⟨after,trace,⟨middleMatch.heap,middleMatch.live,middleMatch.base⟩,rfl,middleOutput,
    wholeHead,wholeLast,?_,wholeChain,?_,?_⟩
  · simpa only [prologueBody_length] using wholeLength
  · simpa only [prologueBody_length] using wholeTime
  · intro state member
    rcases wholeMembers state member with inBody|equal
    · obtain ⟨count,_,run⟩ := body_trace_prefix input prologueBody initial middle body bodyLast
        bodyExecute bodyStrict state inBody
      exact prefixBounds count state run
    · subst state
      exact afterBounds

theorem raw_bounded_prologue_trace (P : Parameters) (fee : ℚ) :
    ∃ (after : State) (trace : List State),
      MemoryMatch after (initializedInputMemory (.natural P.certificate.stages) (.natural P.tools)
        (.rational P.certificate.gamma) (.rational P.certificate.risk) (.rational P.reviewFee) (.rational fee)) ∧
      after.pc=pc 1 ∧ after.output=[] ∧ trace.head?=some initial ∧
      trace.getLast?=some after ∧ trace.length=89 ∧
      trace.IsChain (fun first later => step program (rawInput P fee) first=some later) ∧
      time program trace≤15*89 ∧ ∀ state∈trace,StateBounds 64 (operandBudget P fee) state := by
  apply bounded_prologue_trace
  · have h := operandBudget_address_bits P fee
    have address : 1+natBits 64=8 := by decide
    omega
  · exact rawInput_cell_bits P fee

end PDROC.D27Prepare.Resources
