module

public import Structure.PSTR_HD_HeadsSlices_064

/-! Physical frames needed by the SAME heads run. Actual control/output
writes preserve the ORIGINAL table/used/failed representation; a real query
producer's >=E prefix frame preserves the actual recorded output invariant. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

theorem endpoint_metadata_after {bits q : Nat} (full : List (Finset (Fin q))) (capWords : Nat) (hq : 0 < q) :
    4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ endpoint full capWords bits := by
  unfold endpoint
  rw [PSTRQueryLayout.endpoint_eq, PSTRCountWorkspace.base_metadata_end q full hq capWords bits]
  unfold PSTRStaticHeap.metadataAddress physicalHeaderWords
  omega

theorem heads_heapRepresents_of_frame {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (old fresh : BitVec bits → BitVec bits)
    (hb : 0 < bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration old)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 3))
    (hframe : ∀ physical < endpoint full capWords bits, fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical)) :
    HeapRepresents q full capWords configuration fresh :=
  PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (endpoint full capWords bits)
    old fresh hb hq rep bitmap hr he (endpoint_metadata_after full capWords hq) hframe

theorem recorded_of_query_frame {bits : Nat} (endpoint q rank : Nat) (entries : List Nat)
    (old fresh : BitVec bits → BitVec bits) (recorded : RecordedHeads endpoint q rank entries old)
    (he : Fits bits (endpoint + 10 + entries.length))
    (hframe : ∀ physical, Fits bits physical → endpoint ≤ physical →
      fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical)) :
    RecordedHeads endpoint q rank entries fresh := by
  constructor
  · rw [hframe endpoint ((by omega : endpoint ≤ endpoint + 10 + entries.length).trans_lt he) le_rfl]
    exact recorded.initialRank
  · rw [hframe (endpoint + 1) ((by omega : endpoint + 1 ≤ endpoint + 10 + entries.length).trans_lt he) (by omega)]
    exact recorded.count
  · rw [hframe (endpoint + 2) ((by omega : endpoint + 2 ≤ endpoint + 10 + entries.length).trans_lt he) (by omega)]
    exact recorded.cursor
  · rw [hframe (endpoint + 3) ((by omega : endpoint + 3 ≤ endpoint + 10 + entries.length).trans_lt he) (by omega)]
    exact recorded.finiteFlag
  · rw [hframe (endpoint + 8) ((by omega : endpoint + 8 ≤ endpoint + 10 + entries.length).trans_lt he) (by omega)]
    exact recorded.outputRank
  · intro position hposition
    rw [hframe (endpoint + 10 + position) ((by omega : endpoint + 10 + position ≤ endpoint + 10 + entries.length).trans_lt he) (by omega)]
    exact recorded.outputEntries position hposition

theorem headsInit_prefix_rep {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 9))
    (hp : state.register .address = BitVec.ofNat bits (endpoint full capWords bits))
    (count : Nat) (hc : count ≤ headsInit.length) :
    HeapRepresents q full capWords configuration
      (executeOps (callInput q full .query) (headsInit.take count) state).heap := by
  apply heads_heapRepresents_of_frame full configuration capWords state.heap _ (by omega) hq rep bitmap hr
    ((show endpoint full capWords bits + 3 ≤ endpoint full capWords bits + 9 by omega).trans_lt he)
  intro physical hphysical
  exact headsInit_prefix_frame (callInput q full .query) _ state hb hp
    ((show endpoint full capWords bits + 8 ≤ endpoint full capWords bits + 9 by omega).trans_lt he)
    physical (hphysical.trans ((Nat.le_add_right _ 9).trans_lt he)) (Or.inl hphysical) count hc

theorem headsAppend_prefix_rep {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords rank : Nat) (entries : List Nat) (state : WordState bits)
    (hb : 0 < bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 10 + entries.length + 1))
    (hp : state.register .address = BitVec.ofNat bits (endpoint full capWords bits))
    (recorded : RecordedHeads (endpoint full capWords bits) q rank entries state.heap)
    (count : Nat) (hc : count ≤ headsAppend.length) :
    HeapRepresents q full capWords configuration
      (executeOps (callInput q full .query) (headsAppend.take count) state).heap := by
  apply heads_heapRepresents_of_frame full configuration capWords state.heap _ hb hq rep bitmap hr
    ((show endpoint full capWords bits + 3 ≤ endpoint full capWords bits + 10 + entries.length + 1 by omega).trans_lt he)
  intro physical hphysical
  exact headsAppend_prefix_frame (callInput q full .query) _ _ state hp recorded.cursor
    ((show endpoint full capWords bits + 2 ≤ endpoint full capWords bits + 10 + entries.length + 1 by omega).trans_lt he)
    ((Nat.le_add_right _ 1).trans_lt he) physical
    (hphysical.trans ((by omega : endpoint full capWords bits ≤ endpoint full capWords bits + 10 + entries.length + 1).trans_lt he))
    (by omega) (by omega) (by omega) count hc

theorem headsFinish_prefix_rep {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 0 < bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 9))
    (hp : state.register .address = BitVec.ofNat bits (endpoint full capWords bits))
    (count : Nat) (hc : count ≤ headsFinish.length) :
    HeapRepresents q full capWords configuration
      (executeOps (callInput q full .query) (headsFinish.take count) state).heap := by
  apply heads_heapRepresents_of_frame full configuration capWords state.heap _ hb hq rep bitmap hr
    ((show endpoint full capWords bits + 3 ≤ endpoint full capWords bits + 9 by omega).trans_lt he)
  intro physical hphysical
  exact headsFinish_prefix_frame (callInput q full .query) _ state hp he physical
    (hphysical.trans ((Nat.le_add_right _ 9).trans_lt he)) (by omega) count hc

theorem headsCorrect_prefix_access {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : 4 + packedCapacityWords q capWords bits < heapWords)
    (count : Nat) (hc : count < headsCorrect.length) :
    packingAccessFits (callInput q full .query) heapWords
      (executeOps (callInput q full .query) (headsCorrect.take count) state) headsCorrect[count] := by
  have hp := PSTRRuntimeAdvance.header_word state _ rep.2.2.1
  have h2 : (BitVec.ofNat bits 2).toNat < heapWords := (Nat.mod_le _ _).trans_lt (by omega)
  have hs : (BitVec.ofNat bits (4 + packedCapacityWords q capWords bits)).toNat < heapWords := (Nat.mod_le _ _).trans_lt hroom
  have hcomm : packedCapacityWords q capWords bits + 4 = 4 + packedCapacityWords q capWords bits := by omega
  change count < 8 at hc
  interval_cases count <;>
    simp_all +decide [headsCorrect, PSTRRuntimeAdvance.program, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat]

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
