module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009aw
public import Structure.PA17_A19QueryBridge_RuntimeSelect_009ax

/-! Concrete281op kernel's derived descent-entry state and whole-exit
physical frame. Every local scratch fact comes from the preceding code;
the initial header1 bound is the same-call materialized stage-node fact. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem core_initial_ready {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (hnode : (state.heap (BitVec.ofNat bits (header + 1))).toNat ≤ size) :
    DescReady full configuration (origin + 190) capWords header base counts parents size size
      (packingRun (callInput q full command) containing (parentSteps size + 26) state) := by
  let rom := callInput q full command
  let parented := packingRun rom containing (parentSteps size) state
  have hp := actual_parent_kernel (core_parent_embedded em) layout command configuration row budget state
    data.represents data.width data.mask data.parentBound data.counts_eq data.parents_eq data.base_eq data.budgetBound
    data.rowWord data.selectedWord data.address data.pc data.active
  have hc := actual_parent_candidateBounded (core_parent_embedded em) layout command configuration state data
  have hn : (parented.heap (BitVec.ofNat bits (header + 1))).toNat ≤ size := by
    rw [actual_parent_frame (core_parent_embedded em) layout command configuration state data (parentSteps size) le_rfl
      (header + 1) (layout.headerFits 1 (by decide)) (.inl (by omega))]
    exact hnode
  have hi := execute_desc_initial_ready layout command configuration parented hp.2.2.2.2 hc hn hp.2.2.1 hp.2.1 hp.1
  rw [run_add, fetched_core_init em rom parented hp.2.1 hp.1]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hi.1

theorem core_initial_frame {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 8 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing (parentSteps size + 26) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  let rom := callInput q full command
  let parented := packingRun rom containing (parentSteps size) state
  let current := (parented.heap (BitVec.ofNat bits (header + 1))).toNat
  have hn : parented.heap (BitVec.ofNat bits (header + 1)) = BitVec.ofNat bits current := by
    simp only [current, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hp := actual_parent_kernel (core_parent_embedded em) layout command configuration row budget state
    data.represents data.width data.mask data.parentBound data.counts_eq data.parents_eq data.base_eq data.budgetBound
    data.rowWord data.selectedWord data.address data.pc data.active
  have hi := descendInit_result rom header q size current parented layout.endpointFits hp.2.2.1
    (hp.2.2.2.2.represents.1.trans layout.size_eq.symm) hp.2.2.2.2.candidates hn
  rw [run_add, fetched_core_init em rom parented hp.2.1 hp.1, hi.2]
  calc
    _ = parented.heap (BitVec.ofNat bits physical) := by
      apply descendInitHeap_frame layout current parented.heap physical hfit
      all_goals rcases hprotect with hlo | hhi <;> dsimp only [nodeSlot, toolSlot, endpoint, childBase] at * <;> omega
    _ = state.heap (BitVec.ofNat bits physical) :=
      actual_parent_frame (core_parent_embedded em) layout command configuration state data (parentSteps size) le_rfl physical hfit hprotect

theorem actual_core_heap_frame {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (hnode : (state.heap (BitVec.ofNat bits (header + 1))).toNat ≤ size)
    (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 8 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing (coreSteps size) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hr := core_initial_ready em layout command configuration state data hnode
  rw [coreSteps, run_add]
  exact (actual_desc_loop_frame (core_desc_embedded em) layout command configuration _ hr (descendSteps size) le_rfl physical hfit
    (hprotect.imp_left (by omega))).trans (core_initial_frame em layout command configuration state data physical hfit hprotect)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
