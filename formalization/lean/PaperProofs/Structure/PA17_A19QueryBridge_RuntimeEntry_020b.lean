module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeEntry_020a

/-! Original allowed command, arbitrary registers, ACTIVEpc0 -> actual
materialized Header/Inputs at ACTIVE621 in the SAME containing run. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeEntry020

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PSTRWordSegments

def cursor {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (allowed : Allowed full configuration command) : Fin (full.length + 1) :=
  ⟨configuration.stage, by
    cases command with
    | query => have hs := allowed.2; omega
    | correct => have hs := allowed.2; omega
    | error => have hs := allowed.2; omega⟩

theorem cursor_val {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (allowed : Allowed full configuration command) :
    (cursor full configuration command allowed).val = configuration.stage := rfl

theorem actual_materialized_header {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (whole : List PackingOp) (cb : PSTRBootstrapSlices.Contains whole)
    (co : PSTROuterCountCode.Contains whole 61)
    (em : PA17A19RuntimeHeader011.Embedded (wordBits full) 539 whole)
    (hq : 0 < q) (hl : LaminarSchedule full) (state : WordState (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration state.heap)
    (hp : state.pc = BitVec.ofNat (wordBits full) 0) (ha : state.halted = false) :
    ∃ steps, 66 ≤ steps ∧
      steps ≤ 8 * CapacityBits.width q + 66 + 501 * (prepareNormalization q full).indexed.nodes.size ∧
      PSTRCountComplete.Complete full configuration 61 (capacity full)
        (packingRun (callInput q full command) whole steps state) ∧
      HeaderReady full configuration (cursor full configuration command allowed) hq
        (packingRun (callInput q full command) whole steps state)
        (packingRun (callInput q full command) whole (steps + 82) state) := by
  obtain ⟨steps, lower, upper, complete⟩ := PSTRArbitraryCount.actual_complete full command
    configuration whole cb co em.words em.pcfit hq hl state rep hp ha
  refine ⟨steps, lower, upper, complete, ?_⟩
  rw [PSTRWordSegments.run_add]
  exact from_counts full command configuration (cursor full configuration command allowed)
    hq hl whole em _ complete rfl

theorem header_clock_bounds {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q)
    (steps : Nat) (lower : 66 ≤ steps)
    (upper : steps ≤ 8 * CapacityBits.width q + 66 + 501 * (prepareNormalization q full).indexed.nodes.size) :
    148 ≤ steps + 82 ∧ steps + 82 ≤ 8 * CapacityBits.width q + 148 + 501 * treeSize q full := by
  simp only [treeSize, ne_of_gt hq, ite_false]
  omega

theorem header_trace_bound {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (state : WordState (wordBits full)) (hq : 0 < q) (steps : Nat)
    (upper : steps ≤ 8 * CapacityBits.width q + 66 + 501 * (prepareNormalization q full).indexed.nodes.size) :
    (packingDynamicTrace (callInput q full command) whole (steps + 82) state).length ≤
      12 * (8 * CapacityBits.width q + 148 + 501 * treeSize q full) := by
  have count := packingDynamicTrace_length_le (callInput q full command) whole (steps + 82) state
  have upper' : steps + 82 ≤ 8 * CapacityBits.width q + 148 + 501 * treeSize q full := by
    simp only [treeSize, ne_of_gt hq, ite_false]
    omega
  exact count.trans (Nat.mul_le_mul_left 12 upper')

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeEntry020
