module

public import Structure.PSTR_HD_SelectedAccess_145
public import Structure.PSTR_HD_ZeroCommandCost_139

/-! Containing-CODE-only actual selected-error102 at ORIGINAL w32/F8192.
The sole internal materialization condition is W12=width, produced by the
real query. No extra original caller field or query oracle is introduced. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRSelectedError
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PSTRReplySpill PSTRCountKernel PSTRWordSegments

structure SelectedPost {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (whole : List PackingOp) (start heapWords : Nat) (state : WordState bits) : Prop where
  pc : (packingRun (callInput q full .error) whole 102 state).pc = BitVec.ofNat bits (5 * (start + 102))
  active : (packingRun (callInput q full .error) whole 102 state).halted = false
  represented : HeapRepresents q full capWords (nextConfiguration q full configuration .error)
    (packingRun (callInput q full .error) whole 102 state).heap
  registers : ReplyRegisters state (packingRun (callInput q full .error) whole 102 state)
  reply : ∀ cursor : configuration.stage < full.length + 1,
    ReplyCorrect q (callback q full ⟨configuration.stage, cursor⟩ configuration.used)
      (replyState q capWords (packingRun (callInput q full .error) whole 102 state))
  capacity : ∀ clock ≤ 102, CapacityPrefixBounded q capWords
    (logicalHeap q capWords (packingRun (callInput q full .error) whole clock state).heap)
  table : ∀ clock ≤ 102, ∀ address < tableWords full.length q (treeSize q full),
    logicalHeap q capWords (packingRun (callInput q full .error) whole clock state).heap address =
      logicalHeap q capWords state.heap address
  high : ∀ clock ≤ 102, ∀ physical, Fits bits physical → PSTRCountWorkspace.base q full capWords bits + 12 ≤ physical →
    (packingRun (callInput q full .error) whole clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical)
  safe : ∀ clock < 102, AtSafe (callInput q full .error) whole heapWords (packingRun (callInput q full .error) whole clock state)
  trace : (packingDynamicTrace (callInput q full .error) whole 102 state).length ≤ 1224

theorem actual_selected {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (whole : List PackingOp) (start heapWords : Nat) (state : WordState bits) (tool : Fin q)
    (hq : 0 < q) (laminar : LaminarSchedule full) (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = some tool)
    (room : Rooms full capWords bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (reply : ReplyCorrect q (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used)
      (replyState q capWords state))
    (savedWidth : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (heapRoom : PSTRCountWorkspace.base q full capWords bits + 12 < heapWords)
    (block : PSTROuterCountCode.BlockAt whole start program) (hwords : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    SelectedPost full configuration capWords whole start heapWords state := by
  let rom := callInput q full .error
  have run : packingRun rom whole 102 state = executeOps rom program state :=
    straight_segment rom whole program start block.1 block.2 program_straight hwords hpcfit state hp ha
  have values := execute_selected full configuration capWords state tool hq laminar allowed choose room rep reply savedWidth
  have access : PrefixOK rom heapWords (fun _ => False) program state :=
    ⟨prefix_access full configuration capWords heapWords state tool hq allowed choose room rep reply savedWidth heapRoom,
      by intro _ _ _ _ h; exact False.elim h⟩
  have frames := prefix_table_high full configuration capWords state tool hq allowed choose room rep reply savedWidth
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, packingDynamicTrace_length_le rom whole 102 state⟩
  · rw [run, executeOps_pc rom program state program_straight, hp, BitVec.ofNat_add_ofNat]
    congr 1
  · rw [run, executeOps_halted]
    exact ha
  · rw [run]
    exact values.1
  · rw [run]
    exact values.2.1
  · intro cursor
    rw [run]
    exact values.2.2
  · intro clock hc
    rw [fetched_prefix rom whole program start block.1 block.2 program_straight hwords hpcfit state hp ha clock hc]
    exact prefix_capacity full configuration capWords state tool hq laminar allowed choose room rep reply savedWidth clock hc
  · intro clock hc address haddr
    rw [fetched_prefix rom whole program start block.1 block.2 program_straight hwords hpcfit state hp ha clock hc]
    exact (frames clock hc).1 address haddr
  · intro clock hc physical hf hhigh
    rw [fetched_prefix rom whole program start block.1 block.2 program_straight hwords hpcfit state hp ha clock hc]
    exact (frames clock hc).2 physical hf hhigh
  · intro clock hc
    exact (straight_prefix_safe rom whole program heapWords start (fun _ => False) block.1 block.2
      program_straight hwords hpcfit state hp ha access clock hc).1

theorem original_rooms {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q) (laminar : LaminarSchedule full) :
    Rooms full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) := by
  have dims := PSTROriginalCountRoom.dimension_rooms full
  have workspace := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq laminar
  refine ⟨?_, PA17PackingBounds043.width_le_bits full.length q,
    PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide), ?_, dims.1, dims.2.1, ?_,
    dims.2.2.2.1, PSTROriginalCountRoom.bitmap_room full 8192 hq⟩
  · have h := PSTROriginalCountRoom.word_lower full.length q
    omega
  · exact (show PSTRCountWorkspace.base q full (capacityWords 8192 full.length q (treeSize q full))
      (indexWidth 32 full.length q) + 12 ≤ PSTRCountWorkspace.base q full (capacityWords 8192 full.length q (treeSize q full))
      (indexWidth 32 full.length q) + 15 by omega).trans_lt workspace.1
  · simpa only [treeSize, ne_of_gt hq, ite_false] using dims.2.2.1

theorem original_heap_room {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q) (laminar : LaminarSchedule full) :
    PSTRCountWorkspace.base q full (capacityWords 8192 full.length q (treeSize q full))
      (indexWidth 32 full.length q) + 12 < PSTRCountAllocation.allocation full := by
  have h := PSTRCountAllocation.endpoint_le full hq laminar
  rw [PSTRQueryLayout.endpoint_eq] at h
  omega

theorem actual_selected_original {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (whole : List PackingOp) (start : Nat) (state : WordState (indexWidth 32 full.length q)) (tool : Fin q)
    (hq : 0 < q) (laminar : LaminarSchedule full) (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = some tool)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap)
    (reply : ReplyCorrect q (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used)
      (replyState q (capacityWords 8192 full.length q (treeSize q full)) state))
    (savedWidth : state.heap (BitVec.ofNat (indexWidth 32 full.length q)
      (PSTRCountWorkspace.base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) + 12)) =
      BitVec.ofNat (indexWidth 32 full.length q) (CapacityBits.width q))
    (block : PSTROuterCountCode.BlockAt whole start program)
    (length : whole.length ≤ 8192) (literal : ∀ value ∈ packingCode whole, value < 65536)
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) (5 * start)) (ha : state.halted = false) :
    SelectedPost full configuration (capacityWords 8192 full.length q (treeSize q full)) whole start
      (PSTRCountAllocation.allocation full) state := by
  have hpow : 2 ^ 32 ≤ 2 ^ indexWidth 32 full.length q :=
    Nat.pow_le_pow_right (by decide) (PSTROriginalCountRoom.word_lower full.length q)
  have hbound : Fits (indexWidth 32 full.length q) 65536 := by unfold Fits; omega
  exact actual_selected full configuration _ whole start _ state tool hq laminar allowed choose
    (original_rooms full hq laminar) rep reply savedWidth (original_heap_room full hq laminar) block
    (fun value hv => (literal value hv).trans hbound) ((show 5 * whole.length ≤ 65536 by omega).trans_lt hbound) hp ha

theorem charged_cost102 {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (whole : List PackingOp) (start heapWords : Nat) (state : WordState bits)
    (post : SelectedPost full configuration capWords whole start heapWords state) :
    1 + (packingCode whole).length + 8 + (packingDynamicTrace (callInput q full .error) whole 102 state).length ≤
      5 * whole.length + 1238 := by
  have h := post.trace
  rw [packingCode_length]
  omega

end PaperProofs.Structure.LaminarTree.PSTRSelectedError
