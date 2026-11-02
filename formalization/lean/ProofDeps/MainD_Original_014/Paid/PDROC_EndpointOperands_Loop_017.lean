module

public import Paid.PDROC_EndpointOperands_Loop_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame

theorem rowStraightCode_length : rowStraightCode.length = 115 := rfl

theorem rowStraight_straight : StraightCode rowStraightCode := by
  intro instruction inside
  change instruction ∈ castRowCode ++ (headerCode rowCommands ++ (pairStoreCode ++ advanceCode)) at inside
  rcases List.mem_append.mp inside with inCast | later
  · exact castRow_straight instruction inCast
  · rcases List.mem_append.mp later with inScalar | later
    · exact headerCode_straight rowCommands instruction inScalar
    · rcases List.mem_append.mp later with inPair | inAdvance
      · exact pairStore_straight instruction inPair
      · rw [advanceCode_split] at inAdvance
        rcases List.mem_append.mp inAdvance with inScalar | inIncrement
        · exact headerCode_straight [.rational .multiply 7 6 7] instruction inScalar
        · exact incrementRow_straight instruction inIncrement

/-- Strengthen the original row components by selecting ONE actual115
prefix trace and its genuine backwards jump. The SAME witness carries
the original cache semantics, every-prefix memory, and literal sources. -/
theorem rowBody_actual_prefix (P : Parameters) (m : ℕ) (program : Program) (input : List Cell)
    (before : State) (base E returnPC testPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (invariant : EndpointValues P E returnPC m values) (stored : StoredCache P E m before)
    (separated : base + 48 ≤ E) (fetched : FetchesCode program before.pc (rowBodyCode testPC)) :
    ∃ trace : List State, ∃ after : State,
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun first later => step program input first = some later) ∧
      time program trace ≤ 2235 ∧ after.pc = testPC ∧ after.register .fresh = .natural base ∧
      Header after base (bodyValues P values m) ∧ EndpointValues P E returnPC (m + 1) (bodyValues P values m) ∧
      StoredCache P E (m + 1) after ∧ after.output = before.output ∧ BelowBase before after base ∧
      (∀ state ∈ trace, RegionMemory before state (endpointRowRegion base E m)) ∧
      (∀ state ∈ trace, ControlledPrefix program input rowStraightCode before testPC state) := by
  obtain ⟨middle, run, position, nextFresh, nextHeader, l1, l2, v1, v2, frame, live, output⟩ :=
    rowStraight_execute_spec P m input before base E returnPC values header fresh invariant separated
  have layout : rowBodyCode testPC = rowStraightCode ++ [.jump testPC] := rfl
  rw [layout] at fetched
  have jumpFetch : program[middle.pc]? = some (.jump testPC) := by
    rw [position]
    exact (fetched 115 (by change 115 < 116; decide)).trans (by rfl)
  have control : step program input middle = some {middle with pc := testPC} := by
    simp [step, jumpFetch, Instruction.execute]
  obtain ⟨trace, head, last, chain, cost, prefixes⟩ := controlledPrefix_trace program input rowStraightCode
    rowStraight_straight before middle testPC fetched.append_left run control
  let after : State := {middle with pc := testPC}
  refine ⟨trace, after, head, last, chain, ?_, rfl, nextFresh, nextHeader, invariant.body,
    stored.advance separated ⟨l1, l2, v1, v2⟩ frame live, output, rowBody_below separated frame live, ?_, prefixes⟩
  · rw [rowStraightCode_length] at cost
    omega
  · intro state member
    exact ControlledPrefix.memory program input rowStraightCode before state testPC (endpointRowRegion base E m)
      (rowStraight_prefix_memory P m input before base E returnPC values header fresh invariant separated)
      (prefixes state member)

end PDROC.EndpointOperands.Loop
