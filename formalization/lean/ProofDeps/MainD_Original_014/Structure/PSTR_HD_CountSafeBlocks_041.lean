module

public import Structure.PSTR_HD_CountPrefixCompose_040

/-! Fixed block certificates for the original counts scratch domain. The
predicate protects all physical words except W0..W7 and the final node cell. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRCountWorkspace PSTRStaticLayout PSTRStaticHeap

def nodeProtected (workspace countsBase node physical : Nat) : Prop :=
  (physical < workspace ∨ workspace + 8 ≤ physical) ∧ physical ≠ countsBase + node

theorem frame_represents {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords countsBase node : Nat)
    (old fresh : BitVec bits → BitVec bits) (hb : 0 < bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration old)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7))
    (hbase : base q full capWords bits + 16 ≤ countsBase)
    (frame : HeapFrame (nodeProtected (base q full capWords bits) countsBase node) old fresh) :
    HeapRepresents q full capWords configuration fresh := by
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords
    (base q full capWords bits) old fresh hb hq rep bitmap hr
    ((show base q full capWords bits + 3 ≤ base q full capWords bits + 7 by omega).trans_lt hw) ?_ ?_
  · rw [base_metadata_end q full hq capWords bits]
    unfold metadataAddress physicalHeaderWords
    omega
  · intro physical hp
    exact frame physical ((show physical ≤ base q full capWords bits + 7 by omega).trans_lt hw) ⟨Or.inl hp, by omega⟩

theorem prefix_represents {bits q : Nat} (full : List (Finset (Fin q))) (rom : PhysicalROM)
    (configuration : Configuration q) (capWords countsBase node heapWords : Nat)
    (ops : List PackingOp) (state : WordState bits) (hb : 0 < bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7))
    (hbase : base q full capWords bits + 16 ≤ countsBase)
    (safe : PrefixOK rom heapWords (nodeProtected (base q full capWords bits) countsBase node) ops state)
    (count : Nat) (hc : count ≤ ops.length) :
    HeapRepresents q full capWords configuration (executeOps rom (ops.take count) state).heap :=
  frame_represents full configuration capWords countsBase node state.heap _ hb hq rep bitmap hr hw hbase (safe.frame count hc)

theorem locator_prefixOK {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords countsBase node heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : base q full capWords bits < heapWords) :
    PrefixOK (callInput q full command) heapWords (nodeProtected (base q full capWords bits) countsBase node)
      PSTRCountWorkspace.program state := by
  apply readOnly_prefixOK _ _ _ _ _ locator_readOnly
  exact PSTRCountWorkspace.prefix_access full command configuration capWords heapWords state rep hroom hb

theorem fields_prefixOK {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords countsBase node heapWords : Nat) (state : WordState bits)
    (field : Fin 9) (position : Nat) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) (hN : Fits bits full.length)
    (hp : position < (chunks q full hq)[field.val].length)
    (hi : state.register .index = BitVec.ofNat bits position) (hroom : base q full capWords bits < heapWords) :
    PrefixOK (callInput q full command) heapWords (nodeProtected (base q full capWords bits) countsBase node)
      (PSTRStaticFields.program field) state := by
  apply readOnly_prefixOK _ _ _ _ _ (fields_readOnly field)
  apply PSTRStaticFields.prefix_access full command configuration capWords heapWords state field position hb hq rep hN hp hi
  have hpos := chunk_in_bounds q full hq field.val position field.isLt hp
  rw [base_metadata_end q full hq capWords bits] at hroom
  unfold metadataAddress at hroom ⊢
  omega

theorem spill_prefixOK {bits : Nat} (rom : PhysicalROM) (workspace countsBase node heapWords : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits workspace)
    (hw : Fits bits (workspace + 7)) (hroom : workspace + 7 < heapWords) :
    PrefixOK rom heapWords (nodeProtected workspace countsBase node) spillProgram state := by
  refine ⟨spill_prefix_access rom state workspace heapWords hp (by omega), ?_⟩
  intro count hc physical hf hprotected
  exact spill_prefix_outside rom workspace state hp hw physical hf hprotected.1 count hc

theorem saveField_prefixOK {bits : Nat} (rom : PhysicalROM) (workspace countsBase node heapWords slot : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits workspace)
    (hw : Fits bits (workspace + 7)) (hslot : slot ≤ 7) (hroom : workspace + 7 < heapWords) :
    PrefixOK rom heapWords (nodeProtected workspace countsBase node) (saveField slot) state := by
  refine ⟨saveField_prefix_access rom slot workspace heapWords state hp (by omega), ?_⟩
  intro count hc physical hf hprotected
  exact saveField_prefix_outside rom slot workspace state hp hw hslot physical hf hprotected.1 count hc

theorem clearLoop_prefixOK {bits : Nat} (rom : PhysicalROM) (workspace countsBase node heapWords : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits (workspace + 5))
    (hw : Fits bits (workspace + 7)) (hroom : workspace + 7 < heapWords) :
    PrefixOK rom heapWords (nodeProtected workspace countsBase node) clearLoop state := by
  refine ⟨clearLoop_prefix_access rom workspace heapWords state hp hroom, ?_⟩
  intro count hc physical hf hprotected
  exact clearLoop_prefix_outside rom workspace state hp hw physical hf hprotected.1 count hc

theorem accumulate_prefixOK {bits : Nat} (rom : PhysicalROM) (workspace countsBase node child heapWords origin : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits workspace)
    (hc : state.register .value = BitVec.ofNat bits child)
    (hb : state.heap (BitVec.ofNat bits workspace) = BitVec.ofNat bits countsBase)
    (hw : Fits bits (workspace + 7)) (hroom : workspace + 7 < heapWords) (hchild : countsBase + child < heapWords) :
    PrefixOK rom heapWords (nodeProtected workspace countsBase node) (accumulate origin) state := by
  refine ⟨accumulate_prefix_access rom origin workspace countsBase child heapWords state hp hc hb hroom hchild, ?_⟩
  intro count hcount physical hf hprotected
  exact accumulate_prefix_outside rom origin workspace state hp hw physical hf hprotected.1 count hcount

theorem finishStores_prefixOK {bits : Nat} (rom : PhysicalROM) (workspace countsBase node heapWords : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits workspace)
    (hb : state.heap (BitVec.ofNat bits workspace) = BitVec.ofNat bits countsBase)
    (hn : state.heap (BitVec.ofNat bits (workspace + 2)) = BitVec.ofNat bits node)
    (hfit : Fits bits (countsBase + node))
    (hroom : workspace + 7 < heapWords) (hnode : countsBase + node < heapWords) :
    PrefixOK rom heapWords (nodeProtected workspace countsBase node) finishStores state := by
  refine ⟨finishStores_prefix_access rom workspace countsBase node heapWords state hp hb hn hroom hnode, ?_⟩
  intro count hc physical hf hprotected
  exact finishStores_prefix_other rom workspace countsBase node state hp hb hn hfit physical hf hprotected.2 count hc

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
