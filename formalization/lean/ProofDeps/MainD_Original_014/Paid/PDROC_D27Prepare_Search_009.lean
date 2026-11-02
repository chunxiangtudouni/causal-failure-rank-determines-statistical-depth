module

public import Paid.PDROC_D27Prepare_Search_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid
open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

namespace PDROC.D27Prepare.Search

open Program Memory

/-- The original endpoint guard includes two real rational macros before
its comparison. The entire fetched page is evaluated; its exit is the
original least M, including M=0. -/
theorem endpoint_guard_page_trace (input : List Cell) (D : CertificateInput) (m : ℕ)
    (range : m ≤ D.M) (before : State) (location : before.pc = Program.pc 5)
    (fresh : before.register .fresh = .natural 0)
    (one : SlotHas before 17 (.rational 1))
    (power : SlotHas before 28 (.rational (D.odds ^ m)))
    (ratio : SlotHas before 29 (.rational D.menuRatio)) :
    ∃ (after : State) (trace : List State), trace.head? = some before ∧
      trace.getLast? = some after ∧ trace.length = 29 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      after.pc = (if m = D.M then Program.pc 7 else Program.pc 6) ∧
      after.heap = Function.update before.heap 32 (.rational (D.menuRatio * (1 + D.odds ^ m))) ∧
      after.live = insert 32 before.live ∧
      after.register .fresh = before.register .fresh ∧ after.output = before.output ∧
      (∀ state ∈ trace, state = after ∨ ∃ count ≤ 27,
        linearExecute input (endpointGuard.take count) before = some state) ∧
      ∃ terminal : State, linearExecute input endpointGuard before = some terminal ∧
        after = {terminal with pc := if m = D.M then Program.pc 7 else Program.pc 6} := by
  let memory := currentMemory before
  let next := (memory.write 32 (.rational (1 + D.odds ^ m))).write 32
    (.rational (D.menuRatio * (1 + D.odds ^ m)))
  have evaluated : slotSequenceEval endpointTestCommands memory = some next :=
    endpointTest_eval D m memory one power ratio
  obtain ⟨computed, bodyRun, matched, computedOutput, computedPc⟩ :=
    slotSequence_realize endpointTestCommands input before memory next
      (currentMemory_match before fresh) evaluated
  have left : SlotHas computed 17 (.rational 1) := by
    apply match_has computed next 17 _ matched
    exact Has.write_other _ 17 32 _ _
      (Has.write_other memory 17 32 _ _ one (by decide)) (by decide)
  have right : SlotHas computed 32 (.rational (D.menuRatio * (1 + D.odds ^ m))) :=
    match_has computed next 32 _ matched (Has.write_same _ _ _)
  let terminal := comparisonResult computed 0 17 32
    (Comparison.rat .lessEqual 1 (D.menuRatio * (1 + D.odds ^ m)))
  have compareRun : linearExecute input (ratCompareSlots .lessEqual 17 32) computed = some terminal :=
    ratCompareSlots_execute input computed 0 17 32 1 (D.menuRatio * (1 + D.odds ^ m)) .lessEqual
      matched.base left.1 right.1
      left.2 right.2
  have execute : linearExecute input endpointGuard before = some terminal := by
    rw [endpointGuard_compiled, PDLower.CalibrationCompute.linearExecute_append,
      bodyRun, Option.bind_some]
    exact compareRun
  have fields := comparisonResult_fields computed 0 17 32
    (Comparison.rat .lessEqual 1 (D.menuRatio * (1 + D.odds ^ m)))
  have guardStraight : StraightCode endpointGuard := by
    rw [endpointGuard_compiled]
    intro instruction member
    rcases List.mem_append.mp member with first | later
    · exact slotSequence_straight endpointTestCommands instruction first
    · exact ratCompareSlots_straight .lessEqual 17 32 instruction later
  have allFetch := fetches_page 5 (by decide)
  have bodyFetch : FetchesCode Program.program before.pc endpointGuard := by
    intro offset inside
    rw [location]
    have fetched := allFetch offset (by change offset < (endpointGuard ++ branch 6 7).length; simp only [List.length_append]; omega)
    exact fetched.trans (List.getElem?_append_left inside)
  have terminalPc : terminal.pc = Program.pc 5 + 27 := by
    dsimp only [terminal]
    rw [fields.2.2.2.2.1, computedPc, location]
    rfl
  have controlFetch : Program.program[terminal.pc]? = some (.branchZero .flag (Program.pc 6) (Program.pc 7)) := by
    rw [terminalPc]
    have fetched := allFetch 27 (by decide)
    exact fetched
  let after := {terminal with pc := if m = D.M then Program.pc 7 else Program.pc 6}
  have control : step Program.program input terminal = some after := by
    have branched := branch_step input terminal (Program.pc 6) (Program.pc 7)
      (if Comparison.rat .lessEqual 1 (D.menuRatio * (1 + D.odds ^ m)) then 1 else 0)
      controlFetch fields.2.2.2.1
    simpa [after, endpoint_guard_boolean D m range] using branched
  obtain ⟨trace, head, last, length, chain, prefixes⟩ :=
    fragment_control_trace input endpointGuard guardStraight before terminal after bodyFetch execute control
  refine ⟨after, trace, head, last, ?_, chain, rfl, ?_, ?_, ?_,
    fields.2.2.2.2.2.trans computedOutput, ?_, terminal, execute, rfl⟩
  · simpa [endpointGuard, ratCompareSlots, PDCompute.Solver.ratBinarySlots,
      PDLower.CalibrationCompute.loadSlot, PDLower.CalibrationCompute.storeSlot] using length
  · change terminal.heap = _
    rw [fields.1, matched.heap]
    simp only [next, SlotMemory.write, Function.update_idem, memory, currentMemory]
  · change terminal.live = _
    rw [fields.2.1, matched.live]
    simp only [next, SlotMemory.write, Finset.insert_idem, memory, currentMemory]
  · change terminal.register .fresh = before.register .fresh
    exact fields.2.2.1.trans (matched.base.trans fresh.symm)
  · simpa [endpointGuard, ratCompareSlots, PDCompute.Solver.ratBinarySlots,
      PDLower.CalibrationCompute.loadSlot, PDLower.CalibrationCompute.storeSlot] using prefixes

end PDROC.D27Prepare.Search
