module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009y

/-! Concrete parent-kernel whole-prefix safety. ParentInputs packages exactly
the previously exposed original-heap and same-call materialized facts; it
contains no Ready, scratch initialization, capacity/selection answer, trace
or all-prefix safety assumption. The real program creates its own Ready. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

structure ParentInputs {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (origin capWords header base counts parents size row budget : Nat) (state : WordState bits) : Prop where
  represents : HeapRepresents q full capWords configuration state.heap
  width : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
    BitVec.ofNat bits (CapacityBits.width q)
  mask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
    lowMask bits (CapacityBits.width q)
  parentBound : ∀ node < size, (state.heap (BitVec.ofNat bits (parents + (node + 1)))).toNat ≤ size
  counts_eq : counts = header - (size + (size + 1))
  parents_eq : parents = header - (size + 1)
  base_eq : base = row + budget * (size + 1) + 1
  budgetBound : budget ≤ q + 1
  rowWord : state.heap (BitVec.ofNat bits header) = BitVec.ofNat bits row
  selectedWord : state.heap (BitVec.ofNat bits (header + 6)) = BitVec.ofNat bits budget
  address : state.register .address = BitVec.ofNat bits header
  pc : state.pc = BitVec.ofNat bits (5 * origin)
  active : state.halted = false

theorem ParentInputs.initial_ready {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state) :
    let after := packingRun (callInput q full command) containing (clearSteps size + 38) state
    ReverseReady full configuration (origin + 59) capWords header base counts parents size size after ∧
      ∀ i < size + 1, after.heap (BitVec.ofNat bits (childBase header q + i)) = BitVec.ofNat bits 0 :=
  actual_initial_ready em layout command configuration row budget state data.represents data.width data.mask data.parentBound
    data.counts_eq data.parents_eq data.base_eq data.budgetBound data.rowWord data.selectedWord data.address data.pc data.active

theorem decoded_of_clearPoint {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (heapWords base count : Nat) (state : WordState bits) (hpcfit : Fits bits (5 * containing.length))
    (point : ClearPoint rom containing heapWords base count state) : DecodedAt rom containing heapWords state := by
  rcases point with ⟨ha, index, hi, hpc, hfetch, haccess, _⟩
  have hsmall : state.pc.toNat + 4 < 5 * containing.length := by rw [hpc]; omega
  refine ⟨ha, hsmall.trans hpcfit, ?_, containing[index], ?_, haccess⟩
  · rw [packingCode_length]
    omega
  · rw [hfetch, decode_encode]

theorem actual_parent_frame {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (clock : Nat) (hc : clock ≤ parentSteps size) (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 8 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  let rom := callInput q full command
  let cleared := packingRun rom containing (clearSteps size) state
  have hinput : 1 < rom.input.length := by simp [rom, callInput, RawTreePreprocessingClaims.rawIncidenceROM]
  have hroom : Fits bits (childBase header q + size + 1) :=
    (show childBase header q + size + 1 ≤ endpoint header q size by unfold endpoint; omega).trans_lt layout.endpointFits
  have halloc : childBase header q + size + 1 ≤ heapWords := by have hh := layout.allocated; unfold endpoint at hh; omega
  have hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size := data.represents.1.trans layout.size_eq.symm
  have hclearFrame (count : Nat) (hcount : count ≤ clearSteps size) :
      (packingRun rom containing count state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    rcases hprotect with hlo | hhi
    · apply actual_clear_leading_frame (parent_clear_embedded em) rom q size header heapWords state hroom halloc hinput hsize rfl
        data.address data.pc data.active count hcount physical
      unfold childBase
      omega
    · exact actual_clear_suffix_frame (parent_clear_embedded em) rom q size header heapWords state hroom halloc hinput hsize rfl
        data.address data.pc data.active count hcount physical hfit hhi
  have hclear := actual_clear_kernel (parent_clear_embedded em) rom q size header state hroom hsize rfl data.address data.pc data.active
  rcases hclear with ⟨ha1, hp1, _, hh1, _, _, _, _⟩
  have hbound : origin + 21 + preparePush.length ≤ containing.length := by
    have hh := em.bound; rw [parentProgramAt_length, preparePush_length] at *; omega
  have hpProtect : ClearProtected (header + 8) 5 (BitVec.ofNat bits physical) := by
    intro i hi
    apply (ofNat_injective_of_fit _ _ hfit
      ((show header + 8 + i ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits)).not.mpr
    rcases hprotect with hlo | hhi
    · omega
    · unfold endpoint childBase at hhi
      omega
  have hprepFrame (count : Nat) (hcount : count ≤ 38) :
      (packingRun rom containing count cleared).heap (BitVec.ofNat bits physical) = cleared.heap (BitVec.ofNat bits physical) :=
    preparePush_actual_frame rom containing (origin + 21) header heapWords cleared hbound (parent_prepare_code em) em.words em.pcfit
      hp1 ha1 layout.oneFits hh1 hinput layout.headerAllocated count hcount _ hpProtect
  by_cases hclearPhase : clock ≤ clearSteps size
  · exact hclearFrame clock hclearPhase
  · let offset := clock - clearSteps size
    rw [show clock = clearSteps size + offset by dsimp only [offset]; omega, run_add]
    by_cases hprepPhase : offset ≤ 38
    · exact (hprepFrame offset hprepPhase).trans (hclearFrame (clearSteps size) le_rfl)
    · have hi := data.initial_ready em layout command configuration state
      have hready : ReverseReady full configuration (origin + 59) capWords header base counts parents size size
          (packingRun rom containing 38 cleared) := by simpa only [run_add] using hi.1
      rw [show offset = 38 + (offset - 38) by omega, run_add]
      exact (actual_reverse_loop_frame (parent_reverse_embedded em) layout command configuration _ hready (offset - 38)
        (by dsimp only [offset] at *; unfold parentSteps at hc; omega) physical hfit hprotect).trans
        ((hprepFrame 38 le_rfl).trans (hclearFrame (clearSteps size) le_rfl))

theorem actual_parent_decoded {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (clock : Nat) (hc : clock < parentSteps size) :
    DecodedAt (callInput q full command) containing heapWords (packingRun (callInput q full command) containing clock state) := by
  let rom := callInput q full command
  let cleared := packingRun rom containing (clearSteps size) state
  have hinput : 1 < rom.input.length := by simp [rom, callInput, RawTreePreprocessingClaims.rawIncidenceROM]
  have hroom : Fits bits (childBase header q + size + 1) :=
    (show childBase header q + size + 1 ≤ endpoint header q size by unfold endpoint; omega).trans_lt layout.endpointFits
  have halloc : childBase header q + size + 1 ≤ heapWords := by have hh := layout.allocated; unfold endpoint at hh; omega
  have hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size := data.represents.1.trans layout.size_eq.symm
  by_cases hclearPhase : clock < clearSteps size
  · exact decoded_of_clearPoint rom containing heapWords _ _ _ em.pcfit
      (actual_clear_prefix_point (parent_clear_embedded em) rom q size header heapWords state hroom halloc hinput hsize rfl
        data.address data.pc data.active clock hclearPhase)
  · have hclear := actual_clear_kernel (parent_clear_embedded em) rom q size header state hroom hsize rfl data.address data.pc data.active
    rcases hclear with ⟨ha1, hp1, _, hh1, _, _, _, _⟩
    let offset := clock - clearSteps size
    rw [show clock = clearSteps size + offset by dsimp only [offset]; omega, run_add]
    by_cases hprepPhase : offset < 38
    · have hbound : origin + 21 + preparePush.length ≤ containing.length := by
        have hh := em.bound; rw [parentProgramAt_length, preparePush_length] at *; omega
      exact decoded_of_clearPoint rom containing heapWords _ _ _ em.pcfit
        (preparePush_actual_point rom containing (origin + 21) header heapWords cleared hbound (parent_prepare_code em) em.words em.pcfit
          hp1 ha1 layout.oneFits hh1 hinput layout.headerAllocated offset (by rwa [preparePush_length]))
    · have hi := data.initial_ready em layout command configuration state
      have hready : ReverseReady full configuration (origin + 59) capWords header base counts parents size size
          (packingRun rom containing 38 cleared) := by simpa only [run_add] using hi.1
      rw [show offset = 38 + (offset - 38) by omega, run_add]
      exact actual_reverse_loop_decoded (parent_reverse_embedded em) layout command configuration _ hready (offset - 38)
        (by dsimp only [offset] at *; unfold parentSteps at hc; omega)

theorem actual_parent_represents {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (clock : Nat) (hc : clock ≤ parentSteps size) :
    HeapRepresents q full capWords configuration (packingRun (callInput q full command) containing clock state).heap := by
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (header + 8) state.heap _
    (by have hb := layout.bits8; omega) layout.positive data.represents layout.bitmap layout.capacityFits
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using layout.headerFits 11 (by decide)) layout.metadata_le
  intro physical hphysical
  exact actual_parent_frame em layout command configuration state data clock hc physical
    ((show physical ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits) (.inl hphysical)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
