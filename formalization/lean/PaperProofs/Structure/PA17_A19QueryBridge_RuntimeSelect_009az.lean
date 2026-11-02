module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ay
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_Init_024a

/-! Complete actual fixed281-op selector, every clock: physical fetch,
decode, finite PC/access and protected heap. The independently verified
literal26-op initialization is consumed after this same run's parent164. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem core_init_decoded {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ReverseHeapData full configuration capWords header base counts parents size state.heap)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 164))) (ha : state.halted = false)
    (clock : Nat) (hc : clock < 26) :
    DecodedAt (callInput q full command) containing heapWords (packingRun (callInput q full command) containing clock state) := by
  have hb : origin + 164 + descendInit.length ≤ containing.length := by
    have hh := em.bound; rw [selectionCoreAt_length, descendInit_length] at *; omega
  have hcl : clock < descendInit.length := by rwa [descendInit_length]
  exact decoded_of_phase (callInput q full command) containing descendInit (origin + 164) heapWords hb (core_init_code em) em.words em.pcfit
    state ha clock hcl
    (PA17A19RuntimeRanks008.straight_prefix _ containing descendInit (origin + 164) hb (core_init_code em) descendInit_straight em.words em.pcfit state hp ha clock hcl.le)
    (PA17A19RuntimeRanks008.prefix_pc _ descendInit (origin + 164) descendInit_straight state hp clock hcl.le)
    (PA17A19RuntimeSelectInit024.access_prefix _ header q size heapWords state layout.endpointFits layout.allocated hh
      (data.represents.1.trans layout.size_eq.symm) data.candidates clock hcl)

theorem core_init_prefixFrame {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ReverseHeapData full configuration capWords header base counts parents size state.heap)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 164))) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ 26) (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 8 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  have hb : origin + 164 + descendInit.length ≤ containing.length := by
    have hh := em.bound; rw [selectionCoreAt_length, descendInit_length] at *; omega
  rw [PA17A19RuntimeRanks008.straight_prefix _ containing descendInit (origin + 164) hb (core_init_code em) descendInit_straight em.words em.pcfit state hp ha clock
    (by rwa [descendInit_length])]
  have hne (target : Nat) (hlo : header + 8 ≤ target) (hhi : target < endpoint header q size) :
      BitVec.ofNat bits physical ≠ BitVec.ofNat bits target := by
    apply (ofNat_injective_of_fit _ _ hfit (hhi.le.trans_lt layout.endpointFits)).not.mpr
    rcases hprotect with hlow | hhigh <;> omega
  apply PA17A19RuntimeSelectInit024.prefix_frame _ header q size state layout.endpointFits hh
    (data.represents.1.trans layout.size_eq.symm) data.candidates (BitVec.ofNat bits physical) ?_ ?_ ?_ ?_ ?_ clock hc
  all_goals apply hne
  all_goals first | omega | (dsimp only [nodeSlot, toolSlot, endpoint, childBase]; omega)

theorem actual_core_prefixFrame {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (hnode : (state.heap (BitVec.ofNat bits (header + 1))).toNat ≤ size)
    (clock : Nat) (hc : clock ≤ coreSteps size) (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 8 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  let rom := callInput q full command
  let parented := packingRun rom containing (parentSteps size) state
  by_cases hparent : clock ≤ parentSteps size
  · exact actual_parent_frame (core_parent_embedded em) layout command configuration state data clock hparent physical hfit hprotect
  · by_cases hinit : clock ≤ parentSteps size + 26
    · have hp := actual_parent_kernel (core_parent_embedded em) layout command configuration row budget state
        data.represents data.width data.mask data.parentBound data.counts_eq data.parents_eq data.base_eq data.budgetBound
        data.rowWord data.selectedWord data.address data.pc data.active
      rw [show clock = parentSteps size + (clock - parentSteps size) by omega, run_add]
      exact (core_init_prefixFrame em layout command configuration parented hp.2.2.2.2 hp.2.2.1 hp.2.1 hp.1
        (clock - parentSteps size) (by omega) physical hfit hprotect).trans
        (actual_parent_frame (core_parent_embedded em) layout command configuration state data (parentSteps size) le_rfl physical hfit hprotect)
    · have hr := core_initial_ready em layout command configuration state data hnode
      rw [show clock = (parentSteps size + 26) + (clock - (parentSteps size + 26)) by omega, run_add]
      exact (actual_desc_loop_frame (core_desc_embedded em) layout command configuration _ hr (clock - (parentSteps size + 26))
        (by unfold coreSteps descendSteps at hc; omega) physical hfit (hprotect.imp_left (by omega))).trans
        (core_initial_frame em layout command configuration state data physical hfit hprotect)

theorem actual_core_decoded {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (hnode : (state.heap (BitVec.ofNat bits (header + 1))).toNat ≤ size)
    (clock : Nat) (hc : clock < coreSteps size) :
    DecodedAt (callInput q full command) containing heapWords (packingRun (callInput q full command) containing clock state) := by
  let rom := callInput q full command
  let parented := packingRun rom containing (parentSteps size) state
  by_cases hparent : clock < parentSteps size
  · exact actual_parent_decoded (core_parent_embedded em) layout command configuration state data clock hparent
  · by_cases hinit : clock < parentSteps size + 26
    · have hp := actual_parent_kernel (core_parent_embedded em) layout command configuration row budget state
        data.represents data.width data.mask data.parentBound data.counts_eq data.parents_eq data.base_eq data.budgetBound
        data.rowWord data.selectedWord data.address data.pc data.active
      rw [show clock = parentSteps size + (clock - parentSteps size) by omega, run_add]
      exact core_init_decoded em layout command configuration parented hp.2.2.2.2 hp.2.2.1 hp.2.1 hp.1 (clock - parentSteps size) (by omega)
    · have hr := core_initial_ready em layout command configuration state data hnode
      rw [show clock = (parentSteps size + 26) + (clock - (parentSteps size + 26)) by omega, run_add]
      exact actual_desc_loop_decoded (core_desc_embedded em) layout command configuration _ hr (clock - (parentSteps size + 26))
        (by unfold coreSteps descendSteps at hc; omega)

theorem actual_core_represents {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (hnode : (state.heap (BitVec.ofNat bits (header + 1))).toNat ≤ size)
    (clock : Nat) (hc : clock ≤ coreSteps size) :
    HeapRepresents q full capWords configuration (packingRun (callInput q full command) containing clock state).heap := by
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (header + 8) state.heap _
    (by have hb := layout.bits8; omega) layout.positive data.represents layout.bitmap layout.capacityFits
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using layout.headerFits 11 (by decide)) layout.metadata_le
  intro physical hphysical
  exact actual_core_prefixFrame em layout command configuration state data hnode clock hc physical
    ((show physical ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits) (.inl hphysical)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
