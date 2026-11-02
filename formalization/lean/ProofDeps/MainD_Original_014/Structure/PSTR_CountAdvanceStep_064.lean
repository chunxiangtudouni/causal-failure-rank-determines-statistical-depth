module

public import Structure.PSTR_NodeCounted_063

/-! The real parent copy, counter update and fetched backward jump turn
the actual Counted state into the next outer invariant. Every preserved
word is related through the same physical heap; no parent/count ROM is used. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountAdvanceStep

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace

theorem actual_advance {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (origin : Nat)
    (node : (prepareNormalization q full).indexed.NodeId)
    (initial current : WordState (indexWidth 32 full.length q)) (whole : List PackingOp)
    (hc : PSTROuterCountCode.Contains whole origin)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (ready : PSTRCountReady.Ready full configuration origin
      (capacityWords 8192 full.length q (treeSize q full)) node.val initial)
    (counted : PSTRNodeCounted.Counted full configuration origin
      (capacityWords 8192 full.length q (treeSize q full)) node initial current) :
    PSTRCountReady.Ready full configuration origin
      (capacityWords 8192 full.length q (treeSize q full)) (node.val + 1)
      (packingRun (callInput q full command) whole 85 current) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let B := countsBase workspace
  let size := (prepareNormalization q full).indexed.nodes.size
  let p := parentsBase workspace size
  let offset := PSTRCountChildRows.flatOffset full node.val
  let degree := ((prepareNormalization q full).indexed.children.get node).size
  let rom := callInput q full command
  let parented := executeOps rom PSTRParentCopy.program current
  let advanced := executeOps rom PSTRCountAdvance.program parented
  let finished := executeOps rom (PSTRCountControl.backBlock (origin + 5)) advanced
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have parent_fit (child : (prepareNormalization q full).indexed.NodeId) : Fits bits (p + child.val + 1) :=
    (show p + child.val + 1 ≤ p + size by have hn := child.isLt; omega).trans_lt rooms.2
  have sentinel_fit : Fits bits p := (Nat.le_add_right _ size).trans_lt rooms.2
  have saved_fit (slot : Nat) (hslot : slot < 4) : Fits bits (workspace + 12 + slot) :=
    (show workspace + 12 + slot ≤ workspace + 15 by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega).trans_lt rooms.1
  have parent_heap := PSTRParentCopy.execute_parent full command configuration capWords current node (by omega) hq
    counted.rep raw.1 counted.index
  have parent_frame (physical : Nat) (hp : physical < p + node.val + 1) :
      parented.heap (BitVec.ofNat bits physical) = current.heap (BitVec.ofNat bits physical) := by
    have hf := PSTRParentCopy.prefix_frame full command configuration capWords current node (by omega) hq
      counted.rep raw.1 counted.index rooms.2 physical hp 50 le_rfl
    rw [List.take_of_length_le (show PSTRParentCopy.program.length ≤ 50 by rw [PSTRParentCopy.program_length])] at hf
    exact hf
  have parent_rep : HeapRepresents q full capWords configuration parented.heap := by
    have hr := PSTROuterMemory.parent_prefix_rep full command configuration capWords current node (by omega) hq counted.rep
      (PSTROriginalCountRoom.bitmap_room full 8192 hq)
      (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) raw.1 counted.index rooms.2 50 le_rfl
    rw [List.take_of_length_le (show PSTRParentCopy.program.length ≤ 50 by rw [PSTRParentCopy.program_length])] at hr
    exact hr
  have parent_pc : parented.pc = BitVec.ofNat bits (5 * (origin + 443)) := by
    rw [executeOps_pc rom PSTRParentCopy.program current PSTRParentCopy.program_straight,
      counted.pc, PSTRParentCopy.program_length, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat bits) (by omega)
  have parent_active : parented.halted = false := by rw [executeOps_halted, counted.active]
  have parent_saved (slot : Nat) (hslot : slot < 4) :
      parented.heap (BitVec.ofNat bits (workspace + 12 + slot)) =
        initial.heap (BitVec.ofNat bits (workspace + 12 + slot)) :=
    (parent_frame _ (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega)).trans
      (counted.frame _ (saved_fit slot hslot) (Or.inr (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega)) (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega))
  have parent_degree : parented.heap (BitVec.ofNat bits (workspace + 4)) = BitVec.ofNat bits degree :=
    (parent_frame _ (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega)).trans counted.degree
  have parent_node : parented.heap (BitVec.ofNat bits (workspace + 14)) = BitVec.ofNat bits node.val := by
    have hs := (parent_saved 2 (by decide)).trans (ready.slots 2 (by decide))
    simpa +decide only [Nat.add_assoc, ↓reduceIte] using hs
  have parent_offset : parented.heap (BitVec.ofNat bits (workspace + 15)) = BitVec.ofNat bits offset := by
    have hs := (parent_saved 3 (by decide)).trans (ready.slots 3 (by decide))
    simpa +decide only [Nat.add_assoc, ↓reduceIte] using hs
  have ad := PSTRCountAdvance.execute_advance full command configuration capWords node.val offset degree parented
    (by omega) hq parent_rep rooms.1 parent_degree parent_node parent_offset
  have advance_rep : HeapRepresents q full capWords configuration advanced.heap := by
    have hr := PSTROuterMemory.advance_prefix_rep full command configuration capWords parented (by omega) hq parent_rep
      (PSTROriginalCountRoom.bitmap_room full 8192 hq)
      (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) rooms.1 32 le_rfl
    rw [List.take_of_length_le (show PSTRCountAdvance.program.length ≤ 32 by rw [PSTRCountAdvance.program_length])] at hr
    exact hr
  have advance_frame (physical : Nat) (hp : Fits bits physical)
      (hout : physical < workspace + 14 ∨ workspace + 16 ≤ physical) :
      advanced.heap (BitVec.ofNat bits physical) = parented.heap (BitVec.ofNat bits physical) := by
    have hf := PSTROuterMemory.advance_prefix_frame full command configuration capWords parented (by omega) hq parent_rep
      rooms.1 physical hp hout 32 le_rfl
    rw [List.take_of_length_le (show PSTRCountAdvance.program.length ≤ 32 by rw [PSTRCountAdvance.program_length])] at hf
    exact hf
  have advance_pc : advanced.pc = BitVec.ofNat bits (5 * (origin + 475)) := by
    rw [executeOps_pc rom PSTRCountAdvance.program parented PSTRCountAdvance.program_straight,
      parent_pc, PSTRCountAdvance.program_length, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat bits) (by omega)
  have advance_active : advanced.halted = false := by rw [executeOps_halted, parent_active]
  have h14 : Fits bits (workspace + 14) := (show workspace + 14 ≤ workspace + 15 by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega).trans_lt rooms.1
  have hne : BitVec.ofNat bits (workspace + 15) ≠ BitVec.ofNat bits (workspace + 14) :=
    (ofNat_injective_of_fit _ _ rooms.1 h14).not.mpr (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega)
  have next_node : advanced.heap (BitVec.ofNat bits (workspace + 14)) = BitVec.ofNat bits (node.val + 1) := by
    rw [ad.2.2.2, PSTRCountAdvance.nextHeap, Function.update_self]
  have next_offset : advanced.heap (BitVec.ofNat bits (workspace + 15)) =
      BitVec.ofNat bits (PSTRCountChildRows.flatOffset full (node.val + 1)) := by
    rw [ad.2.2.2, PSTRCountAdvance.nextHeap, Function.update_of_ne hne, Function.update_self]
    exact congrArg (BitVec.ofNat bits) (PSTRCountChildRows.offset_succ full node).symm
  have back_heap : finished.heap = advanced.heap := (PSTRCountControl.back_payload rom (origin + 5) advanced).1
  have ps := PSTROuterCountCode.parent_at whole origin hc
  have ads := PSTROuterCountCode.advance_at whole origin hc
  have bs := PSTROuterCountCode.back_at whole origin hc
  have parent_run := PSTRParentCopy.containing_run rom whole (origin + 393) ps.bound ps.code hwords hpcfit
    current counted.pc counted.active
  have advance_run := PSTRCountAdvance.containing_run rom whole (origin + 443) ads.bound ads.code hwords hpcfit
    parented parent_pc parent_active
  have back_run := PSTRCountControl.fetched_back rom whole (origin + 475) (origin + 5) bs.bound bs.code hwords hpcfit
    advanced advance_pc advance_active
  rw [show 85 = 50 + (32 + 3) from rfl, PSTRWordSegments.run_add, parent_run,
    PSTRWordSegments.run_add, advance_run, back_run]
  constructor
  · rw [back_heap]
    exact advance_rep
  · rw [executeOps_halted, advance_active]
  · exact PSTRCountControl.back_pc rom (origin + 5) advanced
  · exact Nat.succ_le_of_lt node.isLt
  · exact (PSTRCountControl.back_payload rom (origin + 5) advanced).2.1.trans ad.2.1
  · intro slot hslot
    rw [back_heap]
    interval_cases slot
    · have hs := (advance_frame (workspace + 12) (saved_fit 0 (by decide)) (Or.inl (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega))).trans
        ((parent_saved 0 (by decide)).trans (ready.slots 0 (by decide)))
      simpa +decide only [Nat.add_zero, ↓reduceIte] using hs
    · have hs := (advance_frame (workspace + 13) (saved_fit 1 (by decide)) (Or.inl (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega))).trans
        ((parent_saved 1 (by decide)).trans (ready.slots 1 (by decide)))
      simpa +decide only [Nat.add_assoc, ↓reduceIte] using hs
    · simpa +decide only [Nat.add_assoc, ↓reduceIte] using next_node
    · simpa +decide only [Nat.add_assoc, ↓reduceIte] using next_offset
  · intro child hchild
    have hfit : Fits bits (B + child.val) :=
      (show B + child.val ≤ p + size by have hn := child.isLt; (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega).trans_lt rooms.2
    rw [back_heap, advance_frame (B + child.val) hfit (Or.inr (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega)),
      parent_frame (B + child.val) (by have hn := child.isLt; (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega), counted.array child.val child.isLt]
    by_cases he : child.val = node.val
    · have hn : child = node := Fin.ext he
      subst child
      rw [ite_eq_left rfl]
    · rw [ite_eq_right he]
      exact ready.counts child (by omega)
  · rw [back_heap, advance_frame p sentinel_fit (Or.inr (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega)),
      parent_frame p (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega), counted.frame p sentinel_fit (Or.inr (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega))
        (by have hn := node.isLt; (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega)]
    exact ready.sentinel
  · intro child hchild
    rw [back_heap, advance_frame (p + child.val + 1) (parent_fit child)
      (Or.inr (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega))]
    by_cases he : child.val = node.val
    · have hn : child = node := Fin.ext he
      subst child
      rw [parent_heap, Function.update_self]
    · rw [parent_frame (p + child.val + 1) (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega),
        counted.frame (p + child.val + 1) (parent_fit child)
          (Or.inr (by (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega))
          (by have hn := node.isLt; (try dsimp only [p, B, parentsBase, countsBase, workspace, capWords, bits, size]); omega)]
      exact ready.parents child (by omega)

end PaperProofs.Structure.LaminarTree.PSTRCountAdvanceStep
