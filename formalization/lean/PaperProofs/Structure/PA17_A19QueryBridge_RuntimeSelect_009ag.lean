module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009af

/-! Candidate safety is produced by the actual whole parent-building run,
not supplied by the original caller. It is sufficient for guarded leaf0
descent safety independently of the later canonical firstSlackChild proof. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem reverseReady_iterations_candidateBounded {bits q origin capWords heapWords header base counts parents size remaining iterations : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size (remaining + iterations) state)
    (bounded : CandidateBounded header q size state.heap) :
    CandidateBounded header q size (packingRun (callInput q full command) containing (105 * iterations) state).heap := by
  induction iterations generalizing state with
  | zero => simpa only [Nat.mul_zero, packingRun] using bounded
  | succ iterations ih =>
    have rd : ReverseReady full configuration origin capWords header base counts parents size ((remaining + iterations) + 1) state := by
      simpa only [Nat.add_assoc] using ready
    have next := reverseReady_step em layout command configuration state rd
    have bnext := reverseReady_candidateBounded em layout command configuration state rd bounded
    rw [show 105 * (iterations + 1) = 105 + 105 * iterations by omega, run_add]
    exact ih _ next bnext

theorem actual_reverse_loop_candidateBounded {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size size state)
    (bounded : CandidateBounded header q size state.heap) :
    CandidateBounded header q size (packingRun (callInput q full command) containing (105 * size + 5) state).heap := by
  let rom := callInput q full command
  let looped := packingRun rom containing (105 * size) state
  have r0 : ReverseReady full configuration origin capWords header base counts parents size (0 + size) state := by
    simpa only [Nat.zero_add] using ready
  have hend : ReverseReady full configuration origin capWords header base counts parents size 0 looped :=
    reverseReady_iterations em layout command configuration state r0
  have hbound := reverseReady_iterations_candidateBounded em layout command configuration state r0 bounded
  rw [run_add, fetched_reverse_test em rom looped hend.pc hend.active,
    executeOps_heap_of_no_store rom (reverseTest origin) looped (reverseTest_noStore origin)]
  exact hbound

theorem actual_parent_candidateBounded {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state) :
    CandidateBounded header q size (packingRun (callInput q full command) containing (parentSteps size) state).heap := by
  let prepared := packingRun (callInput q full command) containing (clearSteps size + 38) state
  have hi := ParentInputs.initial_ready em layout command configuration state data
  have hz : CandidateBounded header q size prepared.heap := by
    constructor
    · simpa only [Nat.add_zero] using hi.2 0 (by omega)
    · intro encoded he
      rw [hi.2 encoded (by omega)]
      simp
  rw [parentSteps, run_add]
  exact actual_reverse_loop_candidateBounded (parent_reverse_embedded em) layout command configuration prepared hi.1 hz

theorem canonical_size_pos (q : Nat) (full : List (Finset (Fin q))) : 0 < (prepareNormalization q full).indexed.nodes.size := by
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt

theorem ReverseLayout.sizePositive {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size) : 0 < size := by
  rw [layout.size_eq]
  simpa only [treeSize, ne_of_gt layout.positive, ite_false] using canonical_size_pos q full

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
