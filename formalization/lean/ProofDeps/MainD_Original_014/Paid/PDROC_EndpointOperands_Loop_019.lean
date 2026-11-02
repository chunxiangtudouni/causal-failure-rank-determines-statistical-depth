module

public import Paid.PDROC_EndpointOperands_Loop_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

/-- Original13 restore instructions and their actual indirect return,
on ONE selected straight trace. The source return/header values are real
live cells; no supplied final state or synthetic transition is used. -/
theorem return_actual_prefix (program : Program) (input : List Cell) (before : State)
    (base E M returnPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (cache : values 0 = .natural E) (stop : values 3 = .natural M)
    (ret : values 1 = .natural returnPC) (fetched : FetchesCode program before.pc returnCode) :
    ∃ trace : List State, ∃ after : State,
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun first later => step program input first = some later) ∧
      time program trace ≤ 225 ∧ after.pc = returnPC ∧ after.register .fresh = .natural base ∧
      after.register .old = .natural returnPC ∧ after.register .address = .natural E ∧
      after.register .index = .natural (2 * M + 3) ∧
      (∀ state ∈ trace, state.heap = before.heap ∧ state.live = before.live ∧ state.output = before.output) ∧
      (∀ state ∈ trace, ControlledPrefix program input returnPrefixCode before returnPC state) := by
  let middle := returnPrefixResult before base M
  let after : State := {middle with pc := returnPC}
  have run := returnPrefix_execute input before base M values header fresh stop
  have fields := returnPrefix_fields before base M
  have retCell : before.heap (base + 1) = .natural returnPC := (header.value 1 (by decide)).trans ret
  have cacheCell : before.heap base = .natural E := by
    simpa only [Nat.add_zero] using (header.value 0 (by decide)).trans cache
  rw [returnCode_split] at fetched
  have jumpFetch : program[middle.pc]? = some (.jumpIndirect .old) := by
    rw [fields.2.2.2.2.2.2.2]
    exact (fetched 13 (by change 13 < 14; decide)).trans (by rfl)
  have old : middle.register .old = .natural returnPC := fields.2.2.2.2.1.trans retCell
  have control : step program input middle = some after :=
    step_jumpIndirect_return program input middle returnPC jumpFetch old
  obtain ⟨trace, head, last, chain, cost, prefixes⟩ := controlledPrefix_trace program input returnPrefixCode
    returnPrefix_straight before middle returnPC fetched.append_left run control
  have literalMemory : ∀ count ≤ returnPrefixCode.length, ∀ state,
      linearExecute input (returnPrefixCode.take count) before = some state →
        state.heap = before.heap ∧ state.live = before.live ∧ state.output = before.output := by
    intro count bound state actual
    change count ≤ 13 at bound
    by_cases final : count = 13
    · have full : returnPrefixCode.take 13 = returnPrefixCode := rfl
      rw [final, full, run] at actual
      have same := Option.some.inj actual
      subst state
      exact ⟨fields.1, fields.2.1, fields.2.2.1⟩
    · exact returnPrefix_memory input before state base M values header fresh stop count (by omega) actual
  refine ⟨trace, after, head, last, chain, ?_, rfl, fields.2.2.2.1.trans fresh, old,
    fields.2.2.2.2.2.1.trans cacheCell, ?_, ?_, prefixes⟩
  · have length : returnPrefixCode.length = 13 := rfl
    rw [length] at cost
    omega
  · simpa only [Nat.mul_comm] using fields.2.2.2.2.2.2.1
  · intro state member
    exact ControlledPrefix.unchanged program input returnPrefixCode before state returnPC literalMemory (prefixes state member)

end PDROC.EndpointOperands.Loop
