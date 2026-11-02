module

public import Paid.PDROC_EndpointOperands_Loop_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

theorem ControlledPrefix.unchanged (program : Program) (input : List Cell)
    (code : List Instruction) (before state : State) (target : ℕ)
    (literal : ∀ count ≤ code.length, ∀ after,
      linearExecute input (code.take count) before = some after →
        after.heap = before.heap ∧ after.live = before.live ∧ after.output = before.output)
    (actual : ControlledPrefix program input code before target state) :
    state.heap = before.heap ∧ state.live = before.live ∧ state.output = before.output := by
  rcases actual with ⟨count, bound, executed⟩ | ⟨middle, executed, _control, same⟩
  · exact literal count bound state executed
  · subst state
    exact literal code.length (Nat.le_refl _) middle (by simpa only [List.take_length] using executed)

/-- The original fetched test and branch, selecting one straight trace
and keeping its actual prefix source alongside exact unchanged memory. -/
theorem rowTest_actual_prefix (program : Program) (input : List Cell) (before : State)
    (base m M bodyPC exitPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (row : values 8 = .natural m) (stop : values 3 = .natural M)
    (fetched : FetchesCode program before.pc (rowTestCode bodyPC exitPC)) :
    ∃ trace : List State, ∃ after : State,
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun first later => step program input first = some later) ∧
      time program trace ≤ 135 ∧ after.pc = (if m ≤ M then bodyPC else exitPC) ∧
      after.register .fresh = .natural base ∧ Header after base values ∧
      (∀ state ∈ trace, state.heap = before.heap ∧ state.live = before.live ∧ state.output = before.output) ∧
      (∀ state ∈ trace, ControlledPrefix program input rowCompareCode before
        (if m ≤ M then bodyPC else exitPC) state) := by
  let middle := rowCompareResult before base m M
  let target := if m ≤ M then bodyPC else exitPC
  let after : State := {middle with pc := target}
  have run := rowCompare_execute input before base m M values header fresh row stop
  have fields := rowCompare_fields before base m M
  rw [rowTest_split] at fetched
  have branchFetch : program[middle.pc]? = some (.branchZero .flag exitPC bodyPC) := by
    rw [fields.2.2.2.2.2]
    exact (fetched 7 (by change 7 < 8; decide)).trans (by rfl)
  have control : step program input middle = some after := by
    unfold step
    rw [branchFetch]
    have flag : middle.register .flag = .natural (if m ≤ M then 1 else 0) := fields.2.2.2.2.1
    by_cases inside : m ≤ M <;> simp [Instruction.execute, flag, Cell.nat?, inside, after, target]
  obtain ⟨trace, head, last, chain, cost, prefixes⟩ := controlledPrefix_trace program input rowCompareCode
    rowCompare_straight before middle target fetched.append_left run control
  have literalMemory : ∀ count ≤ rowCompareCode.length, ∀ state,
      linearExecute input (rowCompareCode.take count) before = some state →
        state.heap = before.heap ∧ state.live = before.live ∧ state.output = before.output := by
    intro count bound state actual
    change count ≤ 7 at bound
    by_cases final : count = 7
    · have full : rowCompareCode.take 7 = rowCompareCode := rfl
      rw [final, full, run] at actual
      have same := Option.some.inj actual
      subst state
      exact ⟨fields.1, fields.2.1, fields.2.2.1⟩
    · exact rowCompare_prefix input before state base m M values header fresh row stop count (by omega) actual
  have nextHeader : Header after base values := by
    apply header.frame
    · intro slot inside
      exact congrFun fields.1 (base + slot)
    · intro address member
      change address ∈ middle.live
      rw [fields.2.1]
      exact member
  refine ⟨trace, after, head, last, chain, ?_, rfl, fields.2.2.2.1.trans fresh, nextHeader, ?_, prefixes⟩
  · have length : rowCompareCode.length = 7 := rfl
    rw [length] at cost
    omega
  · intro state member
    exact ControlledPrefix.unchanged program input rowCompareCode before state target literalMemory (prefixes state member)

end PDROC.EndpointOperands.Loop
