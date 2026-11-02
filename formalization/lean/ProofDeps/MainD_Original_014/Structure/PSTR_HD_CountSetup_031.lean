module

public import Structure.PSTR_HD_CountWordBlocks_030

/-! The fixed setup actually spills the incoming internal values, reads
original degree/internal metadata and initializes k/sum to zero in scratch.
No degree or internal flag is supplied as an original input field. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine AlgorithmClaims.PackedCapacityRAM
open PSTRCountWorkspace PSTRStaticHeap PSTRStaticLayout

def setupHeap {bits : Nat} (workspace degree internal : Nat) (state : WordState bits) : BitVec bits → BitVec bits :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (entryHeap workspace state) (BitVec.ofNat bits (workspace + 4)) (BitVec.ofNat bits degree))
        (BitVec.ofNat bits (workspace + 5)) (BitVec.ofNat bits internal))
      (BitVec.ofNat bits (workspace + 6)) (BitVec.ofNat bits 0))
    (BitVec.ofNat bits (workspace + 7)) (BitVec.ofNat bits 0)

theorem execute_saveField {bits : Nat} (rom : PhysicalROM) (slot workspace : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits workspace) :
    let result := executeOps rom (saveField slot) state
    result.heap = Function.update state.heap (BitVec.ofNat bits (workspace + slot)) (state.register .value) ∧
    result.register .address = BitVec.ofNat bits (workspace + slot) ∧
    result.register .index = state.register .index := by
  simp +decide [saveField, executeOps, packingExecuteOp, wordOp, wordInstruction, hp, BitVec.ofNat_add_ofNat]

theorem execute_clearLoop {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits (workspace + 5)) :
    (executeOps rom clearLoop state).heap = Function.update
      (Function.update state.heap (BitVec.ofNat bits (workspace + 6)) (BitVec.ofNat bits 0))
      (BitVec.ofNat bits (workspace + 7)) (BitVec.ofNat bits 0) := by
  simp +decide [clearLoop, executeOps, packingExecuteOp, wordOp, wordInstruction, hp,
    BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem setup_index {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom setup state).register .index = state.register .index := by rfl

theorem execute_setup_heap {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : Fits bits full.length) (hi : state.register .index = BitVec.ofNat bits node.val)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7)) :
    (executeOps (callInput q full command) setup state).heap =
      setupHeap (base q full capWords bits) ((prepareNormalization q full).indexed.children.get node).size
        (bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) state := by
  let rom := callInput q full command
  let workspace := base q full capWords bits
  let degree := ((prepareNormalization q full).indexed.children.get node).size
  let internal := bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)
  have hw3 : Fits bits (workspace + 3) := (show workspace + 3 ≤ workspace + 7 by omega).trans_lt hw
  let s0 := executeOps rom bootstrap state
  have h0 := execute_bootstrap full command configuration capWords state hb hq rep
  have r0 : HeapRepresents q full capWords configuration s0.heap := by
    rw [h0.1]
    exact entry_represents full configuration capWords state (by omega) hq rep bitmap hr hw3
  have i0 : s0.register .index = BitVec.ofNat bits node.val := h0.2.2.2.1.trans hi
  let s1 := executeOps rom (PSTRStaticFields.program ⟨2, by decide⟩) s0
  have h1 := PSTRStaticFields.execute_field full command configuration capWords s0 ⟨2, by decide⟩ node.val
    hb hq r0 hN (by simp [chunks]) i0
  have v1 : s1.register .value = BitVec.ofNat bits degree := by
    simpa [chunks, mapped_finRange_get, degree, s1, rom] using h1.1
  have r1 : HeapRepresents q full capWords configuration s1.heap := by rw [h1.2.2.2]; exact r0
  let s2 := executeOps rom PSTRCountWorkspace.program s1
  have h2 := execute_base full command configuration capWords s1 hb hq r1
  let s3 := executeOps rom (saveField 4) s2
  have h3 := execute_saveField rom 4 workspace s2 h2.1
  have v2 : s2.register .value = BitVec.ofNat bits degree := h2.2.1.trans v1
  have r2 : HeapRepresents q full capWords configuration s2.heap := by rw [h2.2.2.2.2.2.1]; exact r1
  have r3 : HeapRepresents q full capWords configuration s3.heap := by
    rw [h3.1]
    exact scratch_store_represents full configuration capWords (workspace + 4) s2.heap (s2.register .value)
      (by omega) hq r2 bitmap hr hw3 ((show workspace + 4 ≤ workspace + 7 by omega).trans_lt hw) (by omega)
  have i3 : s3.register .index = BitVec.ofNat bits node.val :=
    h3.2.2.trans (h2.2.2.1.trans (h1.2.2.1.trans i0))
  let s4 := executeOps rom (PSTRStaticFields.program ⟨5, by decide⟩) s3
  have h4 := PSTRStaticFields.execute_field full command configuration capWords s3 ⟨5, by decide⟩ node.val
    hb hq r3 hN (by simp [chunks]) i3
  have v4 : s4.register .value = BitVec.ofNat bits internal := by
    simpa [chunks, mapped_finRange_get, internal, s4, rom] using h4.1
  have r4 : HeapRepresents q full capWords configuration s4.heap := by rw [h4.2.2.2]; exact r3
  let s5 := executeOps rom PSTRCountWorkspace.program s4
  have h5 := execute_base full command configuration capWords s4 hb hq r4
  let s6 := executeOps rom (saveField 5) s5
  have h6 := execute_saveField rom 5 workspace s5 h5.1
  have v5 : s5.register .value = BitVec.ofNat bits internal := h5.2.1.trans v4
  have h7 := execute_clearLoop rom workspace s6 h6.2.1
  simp only [setup, executeOps_append]
  change (executeOps rom clearLoop s6).heap = setupHeap workspace degree internal state
  rw [h7, h6.1, v5, h5.2.2.2.2.2.1, h4.2.2.2, h3.1, v2,
    h2.2.2.2.2.2.1, h1.2.2.2, h0.1]
  rfl

theorem setupHeap_prefix_frame {bits : Nat} (workspace degree internal : Nat) (state : WordState bits)
    (hw : Fits bits (workspace + 7)) :
    ∀ physical < workspace,
      setupHeap workspace degree internal state (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  intro physical hp
  unfold setupHeap
  rw [store_prefix_frame _ workspace (workspace + 7) _ (by omega) hw physical hp,
    store_prefix_frame _ workspace (workspace + 6) _ (by omega) ((by omega : workspace + 6 ≤ workspace + 7).trans_lt hw) physical hp,
    store_prefix_frame _ workspace (workspace + 5) _ (by omega) ((by omega : workspace + 5 ≤ workspace + 7).trans_lt hw) physical hp,
    store_prefix_frame _ workspace (workspace + 4) _ (by omega) ((by omega : workspace + 4 ≤ workspace + 7).trans_lt hw) physical hp]
  exact entry_prefix_frame workspace state ((by omega : workspace + 3 ≤ workspace + 7).trans_lt hw) physical hp

theorem setupHeap_represents {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords degree internal : Nat) (state : WordState bits)
    (hb : 0 < bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7)) :
    HeapRepresents q full capWords configuration (setupHeap (base q full capWords bits) degree internal state) := by
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords
    (base q full capWords bits) state.heap _ hb hq rep bitmap hr
    ((show base q full capWords bits + 3 ≤ base q full capWords bits + 7 by omega).trans_lt hw) ?_
    (setupHeap_prefix_frame _ degree internal state hw)
  rw [base_metadata_end q full hq capWords bits]
  unfold metadataAddress physicalHeaderWords
  omega

def slotValue {bits : Nat} (degree internal count total : Nat) (initial : WordState bits) : Nat → BitVec bits
  | 0 => initial.register .old
  | 1 => initial.register .fresh
  | 2 => initial.register .index
  | 3 => initial.register .value
  | 4 => BitVec.ofNat bits degree
  | 5 => BitVec.ofNat bits internal
  | 6 => BitVec.ofNat bits count
  | _ => BitVec.ofNat bits total

def HasSlots {bits : Nat} (workspace degree internal count total : Nat)
    (initial : WordState bits) (heap : BitVec bits → BitVec bits) : Prop :=
  ∀ slot < 8, heap (BitVec.ofNat bits (workspace + slot)) = slotValue degree internal count total initial slot

theorem setupHeap_slots {bits : Nat} (workspace degree internal : Nat) (initial : WordState bits)
    (hw : Fits bits (workspace + 7)) :
    HasSlots workspace degree internal 0 0 initial (setupHeap workspace degree internal initial) := by
  have he (a b : Nat) (ha : a ≤ workspace + 7) (hb : b ≤ workspace + 7) :
      BitVec.ofNat bits a = BitVec.ofNat bits b ↔ a = b :=
    ofNat_injective_of_fit a b (ha.trans_lt hw) (hb.trans_lt hw)
  intro slot hs
  interval_cases slot <;>
    simp (disch := omega) [setupHeap, entryHeap, Function.update_apply, he, slotValue]

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
