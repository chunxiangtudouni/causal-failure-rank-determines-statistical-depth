module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009w

/-! The actual clear21 and prepare38 establish the reverse invariant and
zero candidate array from arbitrary incoming local scratch. Materialized
parents/cache and the actual ranked header are internal same-call facts. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_initial_ready {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (row budget : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hparentBound : ∀ node < size, (state.heap (BitVec.ofNat bits (parents + (node + 1)))).toNat ≤ size)
    (hcounts : counts = header - (size + (size + 1))) (hparents : parents = header - (size + 1))
    (hbase : base = row + budget * (size + 1) + 1) (hbudget : budget ≤ q + 1)
    (hrow : state.heap (BitVec.ofNat bits header) = BitVec.ofNat bits row)
    (hselected : state.heap (BitVec.ofNat bits (header + 6)) = BitVec.ofNat bits budget)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let after := packingRun (callInput q full command) containing (clearSteps size + 38) state
    ReverseReady full configuration (origin + 59) capWords header base counts parents size size after ∧
      ∀ i < size + 1, after.heap (BitVec.ofNat bits (childBase header q + i)) = BitVec.ofNat bits 0 := by
  let rom := callInput q full command
  let cleared := packingRun rom containing (clearSteps size) state
  let prepared := executeOps rom preparePush cleared
  have hinput : 1 < rom.input.length := by simp [rom, callInput, RawTreePreprocessingClaims.rawIncidenceROM]
  have hclearRoom : Fits bits (childBase header q + size + 1) :=
    (show childBase header q + size + 1 ≤ endpoint header q size by unfold endpoint; omega).trans_lt layout.endpointFits
  have hclearAlloc : childBase header q + size + 1 ≤ heapWords := by
    have hh := layout.allocated
    unfold endpoint at hh
    omega
  have hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size := rep.1.trans layout.size_eq.symm
  have hc := actual_clear_kernel (parent_clear_embedded em) rom q size header state hclearRoom hsize rfl hh hp ha
  rcases hc with ⟨ha1, hpc1, hm1, hh1, _, _, _, _⟩
  have hclearFrame (physical : Nat) (hphysical : physical < header + 8) :
      cleared.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    apply actual_clear_leading_frame (parent_clear_embedded em) rom q size header heapWords state hclearRoom hclearAlloc
      hinput hsize rfl hh hp ha (clearSteps size) le_rfl physical
    unfold childBase
    omega
  have hlower : size + (size + 1) ≤ header := by
    have hh := layout.header_eq
    rw [← layout.size_eq] at hh
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase at hh
    omega
  have hprep := preparePush_result rom q size header row budget cleared hclearRoom hlower hbudget
    (by rw [hclearFrame 0 (by omega)]; exact hsize) rfl hh1
    (by rw [hclearFrame header (by omega)]; exact hrow)
    (by rw [hclearFrame (header + 6) (by omega)]; exact hselected)
  rcases hprep with ⟨had2, _, _, hm2⟩
  have hrun : packingRun rom containing (clearSteps size + 38) state = prepared := by
    rw [run_add]
    exact fetched_parent_prepare em rom cleared hpc1 ha1
  have hbound : origin + 21 + preparePush.length ≤ containing.length := by
    have hb := em.bound
    rw [parentProgramAt_length, preparePush_length] at *
    omega
  have hprepFrame (address : BitVec bits) (hprotect : ClearProtected (header + 8) 5 address) :
      prepared.heap address = cleared.heap address := by
    have hf := preparePush_actual_frame rom containing (origin + 21) header heapWords cleared hbound (parent_prepare_code em)
      em.words em.pcfit hpc1 ha1 layout.oneFits hh1 hinput layout.headerAllocated 38 le_rfl address hprotect
    rw [fetched_parent_prepare em rom cleared hpc1 ha1] at hf
    exact hf
  have hprepLeading (physical : Nat) (hphysical : physical < header + 8) :
      prepared.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    apply (hprepFrame _ ?_).trans (hclearFrame physical hphysical)
    intro i hi
    apply (ofNat_injective_of_fit _ _
      ((show physical ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits)
      ((show header + 8 + i ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits)).not.mpr
    omega
  have hrep : HeapRepresents q full capWords configuration prepared.heap := by
    apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (header + 8) state.heap prepared.heap
      (by have hb := layout.bits8; omega) layout.positive rep layout.bitmap layout.capacityFits
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using layout.headerFits 11 (by decide)) layout.metadata_le hprepLeading
  have hcells := preparedPushHeap_cells q size header row budget cleared.heap (layout.headerFits 13 (by decide))
  dsimp only at hcells
  rw [← hm2] at hcells
  dsimp only
  rw [hrun]
  constructor
  · refine ⟨le_rfl, had2, hcells.1, ?_, ?_, ?_⟩
    · rw [executeOps_pc rom preparePush cleared preparePush_straight, hpc1, preparePush_length, BitVec.ofNat_add_ofNat]
      congr 1
    · rw [executeOps_halted, ha1]
    · refine ⟨hrep, ?_, ?_, ?_, hcells.2.2.1, ?_, ?_, ?_⟩
      · rw [hprepLeading _ (layout.cache_lt 12 (by decide))]
        exact hwidth
      · rw [hprepLeading _ (layout.cache_lt 13 (by decide))]
        exact hmask
      · simpa only [← hbase] using hcells.2.1
      · simpa only [← hcounts] using hcells.2.2.2.1
      · simpa only [← hparents] using hcells.2.2.2.2
      · intro node hnode
        rw [hprepLeading _ (by have hh := layout.parentsEnd; omega)]
        exact hparentBound node hnode
  · intro i hi
    rw [hprepFrame _ ?_, hm1]
    · exact clearHeap_zero (childBase header q) (size + 1) state.heap
        (by simpa only [Nat.add_assoc] using hclearRoom) i hi
    · intro j hj
      apply (ofNat_injective_of_fit _ _
        ((show childBase header q + i ≤ endpoint header q size by unfold endpoint; omega).trans_lt layout.endpointFits)
        ((show header + 8 + j ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits)).not.mpr
      unfold childBase
      omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
