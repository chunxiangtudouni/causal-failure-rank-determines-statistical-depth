module

public import Structure.PA17_A19QueryBridge_RuntimeHeader_011f
public import Structure.PSTR_RepairHeap_024

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRStaticLayout PSTRStaticHeap PSTRWordSegments

def logicalHead {q : Nat} (full : List (Finset (Fin q))) (capWords : Nat) : Nat :=
  PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)

theorem head_views {bits q : Nat} (full : List (Finset (Fin q))) (capWords : Nat) :
    capWords ≤ logicalHead full capWords ∧
    head full capWords bits = physicalHeaderWords + packedCapacityWords q capWords bits +
      (logicalHead full capWords - capWords) := by
  unfold head logicalHead PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    PSTRQueryLayout.physicalWorkspace PSTRQueryLayout.logicalWorkspace metadataAddress
  omega

theorem header_logical_word {bits q : Nat} (full : List (Finset (Fin q))) (capWords : Nat)
    (heap : BitVec bits → BitVec bits) (hq : 0 < q) (i : Nat) :
    logicalHeap q capWords heap (logicalHead full capWords + i) =
      (heap (BitVec.ofNat bits (head full capWords bits + i))).toNat := by
  have hh := head_views (bits := bits) full capWords
  have he : logicalHead full capWords + i = capWords + (logicalHead full capWords - capWords + i) := by omega
  rw [he, PSTRStaticHeap.logical_suffix heap capWords _ hq]
  have hp : physicalHeaderWords + packedCapacityWords q capWords bits +
      (logicalHead full capWords - capWords + i) = head full capWords bits + i := by omega
  rw [hp]

theorem logical_prefix_frame {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hscalar : Fits bits (4 + capWords * CapacityBits.width q))
    (hf : Fits bits (head full capWords bits + 3)) (address count : Nat)
    (ha : address < logicalHead full capWords) :
    logicalHeap q capWords (executeOps (callInput q full command) (program.take count) state).heap address =
      logicalHeap q capWords state.heap address := by
  have hh := head_views (bits := bits) full capWords
  simp only [physicalHeaderWords] at hh
  exact PSTRRepairHeap.logical_frame _ _ capWords (logicalHead full capWords - capWords)
    (head full capWords bits) address (by omega) hq hscalar hf (by omega)
    (prefix_frame full command configuration capWords state hb hq rep hf · count) (by omega)

theorem heap_represents {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hscalar : Fits bits (4 + capWords * CapacityBits.width q))
    (hf : Fits bits (head full capWords bits + 3)) (count : Nat) :
    HeapRepresents q full capWords configuration
      (executeOps (callInput q full command) (program.take count) state).heap := by
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (head full capWords bits)
    state.heap _ (by omega) hq rep bitmap hscalar hf ?_
    (prefix_frame full command configuration capWords state hb hq rep hf · count)
  unfold head PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    PSTRQueryLayout.physicalWorkspace metadataAddress physicalHeaderWords
  omega

theorem writeHeader_upper_frame {bits : Nat} (rom : PhysicalROM) (header : Nat)
    (state : WordState bits) (ha : state.register .address = BitVec.ofNat bits header)
    (hf : Fits bits (header + 3)) (physical count : Nat)
    (hphysical : Fits bits physical) (habove : header + 3 < physical) :
    (executeOps rom (writeHeader.take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hbound : header + 3 < 2 ^ bits := hf
  have hfit : physical < 2 ^ bits := hphysical
  have hne (i : Nat) (hi : i ≤ 3) : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (header + i) := by
    intro he
    have hv := congrArg BitVec.toNat he
    rw [show (BitVec.ofNat bits physical).toNat = physical from Nat.mod_eq_of_lt hfit,
      show (BitVec.ofNat bits (header + i)).toNat = header + i from Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have hzero : BitVec.ofNat bits physical ≠ BitVec.ofNat bits header := by
    simpa only [Nat.add_zero] using hne 0 (by omega)
  by_cases hc : count < writeHeader.length
  · change count < 10 at hc
    interval_cases count <;>
      simp +decide [writeHeader, executeOps, packingExecuteOp, wordOp, wordInstruction,
        ha, BitVec.ofNat_add_ofNat, Nat.add_assoc, hne, hzero]
  · rw [List.take_of_length_le (by omega)]
    simp +decide [writeHeader, executeOps, packingExecuteOp, wordOp, wordInstruction,
      ha, BitVec.ofNat_add_ofNat, Nat.add_assoc, hne, hzero]

/-- HD owns endpoint E and every word above it. Every REAL header prefix
preserves those addresses, including its four stores and ACTIVE exit. -/
theorem endpoint_frame {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hf : Fits bits (head full capWords bits + 3)) (physical count : Nat)
    (hphysical : Fits bits physical)
    (hE : PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) q ≤ physical) :
    (executeOps (callInput q full command) (program.take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have habove : head full capWords bits + 3 < physical := by
    unfold head PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags at *
    omega
  rw [program_split]
  by_cases hc : count ≤ prelude.length
  · rw [List.take_append_of_le_length hc, prelude_prefix_heap]
  · rw [List.take_append, List.take_of_length_le (by omega), executeOps_append]
    rw [writeHeader_upper_frame _ _ _ (prelude_address full command configuration capWords state hb hq rep)
      hf physical _ hphysical habove, execute_prelude_heap]

theorem actual_endpoint_frame {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hf : Fits bits (head full capWords bits + 3))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 82) (physical : Nat) (hphysical : Fits bits physical)
    (hE : PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) q ≤ physical) :
    (packingRun (callInput q full command) containing count state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  rw [actual_prefix em _ state hp ha count (by simpa only [program_length] using hc)]
  exact endpoint_frame full command configuration capWords state hb hq rep hf physical count hphysical hE

/-- The original table bound and the shared counts-parent-header ABI supply
ReadBounds, with no extra table-read oracle or dimension qualification. -/
theorem read_bounds {q : Nat} (full : List (Finset (Fin q))) (capWords : Nat)
    (stage : Fin (full.length + 1))
    (htable : tableWords full.length q (treeSize q full) ≤ capWords) :
    let W := PSTRQueryLayout.logicalWorkspace full capWords
    PA17QueryTests009.ReadBounds (treeSize q full) q (logicalHead full capWords)
      (PSTRQueryLayout.countsBase W) (PSTRQueryLayout.parentsBase W (treeSize q full))
      (logicalHead full capWords + 1) (row full stage) (logicalHead full capWords + 4) := by
  have hr := PA17QueryBudget015.row_fits_table full.length q (treeSize q full) (PA17QueryBudget015.rowIndex full stage)
  have hh := head_views (bits := 0) full capWords
  have hl := PSTRQueryLayout.read_bounds (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)
  exact ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2, hr.trans (htable.trans (by omega))⟩

/-- Composition with the counts/parent materialization in the SAME call.
The table is obtained from ORIGINAL HeapRepresents; only the separately
executed counts/parent pass supplies its genuine array facts. Nothing here
is added to the original MachineControllerClaims input qualifications. -/
theorem internal_inputs {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (stage : Fin (full.length + 1)) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hstage : configuration.stage = stage.val)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hscalar : Fits bits (4 + capWords * CapacityBits.width q))
    (hN : Fits bits full.length) (hqr : Fits bits (q + 2))
    (htr : Fits bits (treeSize q full + 1))
    (hrr : Fits bits ((stage.val + 1) * (q + 2)))
    (hr : Fits bits (row full stage)) (hf : Fits bits (head full capWords bits + 3))
    (counts : ∀ target : (prepareNormalization q full).indexed.NodeId,
      logicalHeap q capWords state.heap
        (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords) + target.val) =
        (IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used).get target)
    (parents : PA17HeapAncestors001.ParentHeapFor (prepareNormalization q full).indexed
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (logicalHeap q capWords state.heap)) :
    let W := PSTRQueryLayout.logicalWorkspace full capWords
    PA17QueryTests009.Inputs (prepareNormalization q full).indexed (logicalHead full capWords)
      (PSTRQueryLayout.countsBase W) (PSTRQueryLayout.parentsBase W (treeSize q full))
      (logicalHead full capWords + 1) (row full stage)
      (IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used)
      (IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage))
      (PA17QueryBudget015.node full hq stage)
      (logicalHeap q capWords (executeOps (callInput q full command) program state).heap) := by
  let after := executeOps (callInput q full command) program state
  have result := execute_result full command configuration capWords state stage hb hq rep hstage hN hqr htr hrr hf
  have values := storedHeap_values state.heap (head full capWords bits)
    (BitVec.ofNat bits (row full stage)) (BitVec.ofNat bits (nodeWord full hq stage))
    (BitVec.ofNat bits (PA17QueryHeader009.active full.length stage.val)) (BitVec.ofNat bits stage.val) hf
  have hframe (address : Nat) (ha : address < logicalHead full capWords) :
      logicalHeap q capWords after.heap address = logicalHeap q capWords state.heap address := by
    simpa only [List.take_length] using
      logical_prefix_frame full command configuration capWords state hb hq rep hscalar hf address program.length ha
  have hrep : HeapRepresents q full capWords configuration after.heap := by
    simpa only [List.take_length] using heap_represents full command configuration capWords state hb hq rep bitmap hscalar hf program.length
  have hnode : Fits bits (nodeWord full hq stage) := by
    have hn := UniformNormalizationRAM.encodedNode_le (prepareNormalization q full).indexed (PA17QueryBudget015.node full hq stage)
    have ht : (prepareNormalization q full).indexed.nodes.size < 2 ^ bits := by
      simp only [treeSize, ne_of_gt hq, ite_false] at htr
      change (prepareNormalization q full).indexed.nodes.size + 1 < 2 ^ bits at htr
      omega
    exact hn.trans_lt ht
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hw := header_logical_word full capWords (executeOps (callInput q full command) program state).heap hq 0
    simp only [Nat.add_zero] at hw
    rw [hw]
    rw [result.2, values.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  · rw [header_logical_word full capWords after.heap hq 1, result.2, values.2.1,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnode]
    rfl
  · intro target
    rw [hframe _ (by
      have ht := target.isLt
      unfold logicalHead PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      simp only [treeSize, ne_of_gt hq, ite_false]
      omega)]
    exact counts target
  · constructor
    · rw [hframe _ (by unfold logicalHead PSTRQueryLayout.header; omega)]
      exact parents.1
    · intro target
      rw [hframe _ (by
        have ht := target.isLt
        unfold logicalHead PSTRQueryLayout.header
        simp only [treeSize, ne_of_gt hq, ite_false]
        omega)]
      exact parents.2 target
  · have ht := (hrep.2.2.2.2.2.2.2.2 hq).1
    simpa only [row, treeSize, ne_of_gt hq, ite_false] using
      PA17QueryBudget015.entries_of_physicalTableCorrect q full (PA17QueryBudget015.rowIndex full stage)
        (logicalHeap q capWords after.heap) ht

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011
