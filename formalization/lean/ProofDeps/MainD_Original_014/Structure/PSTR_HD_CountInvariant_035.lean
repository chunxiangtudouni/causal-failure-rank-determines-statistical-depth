module

public import Structure.PSTR_HD_CountFetch_034

/-! The loop invariant refers only to actual workspace words and the real
physical counts array. Its accumulated sum is a mathematical description of
the child reads that the fixed kernel has already performed. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine AlgorithmClaims.PackedCapacityRAM
open PSTRCountWorkspace PSTRStaticHeap PSTRStaticLayout PSTRCountBounds

structure LoopData {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords countsBase offset : Nat) (node : (prepareNormalization q full).indexed.NodeId)
    (initial : WordState bits) (count : Nat) (state : WordState bits) : Prop where
  rep : HeapRepresents q full capWords configuration state.heap
  slots : HasSlots (base q full capWords bits) ((prepareNormalization q full).indexed.children.get node).size
    (bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) count
    (prefixSum full initial.heap countsBase offset count) initial state.heap
  array : ∀ child < (prepareNormalization q full).indexed.nodes.size,
    state.heap (BitVec.ofNat bits (countsBase + child)) = initial.heap (BitVec.ofNat bits (countsBase + child))
  outside : ∀ physical, Fits bits physical →
    (physical < base q full capWords bits ∨ base q full capWords bits + 8 ≤ physical) →
    state.heap (BitVec.ofNat bits physical) = initial.heap (BitVec.ofNat bits physical)
  counter : count ≤ ((prepareNormalization q full).indexed.children.get node).size
  active : state.halted = false

theorem setupHeap_outside {bits : Nat} (workspace degree internal : Nat) (state : WordState bits)
    (hw : Fits bits (workspace + 7)) (physical : Nat) (hp : Fits bits physical)
    (hout : physical < workspace ∨ workspace + 8 ≤ physical) :
    setupHeap workspace degree internal state (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  unfold setupHeap
  rw [store_other _ (workspace + 7) physical _ hw hp (by omega),
    store_other _ (workspace + 6) physical _ ((show workspace + 6 ≤ workspace + 7 by omega).trans_lt hw) hp (by omega),
    store_other _ (workspace + 5) physical _ ((show workspace + 5 ≤ workspace + 7 by omega).trans_lt hw) hp (by omega),
    store_other _ (workspace + 4) physical _ ((show workspace + 4 ≤ workspace + 7 by omega).trans_lt hw) hp (by omega)]
  exact entry_outside workspace state ((show workspace + 3 ≤ workspace + 7 by omega).trans_lt hw) physical hp (by omega)

theorem setup_data {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords countsBase offset : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (initial : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration initial.heap)
    (hN : Fits bits full.length) (hi : initial.register .index = BitVec.ofNat bits node.val)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7))
    (hbase : base q full capWords bits + 16 ≤ countsBase)
    (hfit : Fits bits (countsBase + (prepareNormalization q full).indexed.nodes.size))
    (ha : initial.halted = false) :
    LoopData full configuration capWords countsBase offset node initial 0
      (executeOps (callInput q full command) setup initial) := by
  have hh := execute_setup_heap full command configuration capWords initial node hb hq rep hN hi bitmap hr hw
  constructor
  · rw [hh]
    exact setupHeap_represents full configuration capWords _ _ initial (by omega) hq rep bitmap hr hw
  · rw [hh]
    simpa only [prefixSum, List.range_zero, List.map_nil, List.sum_nil] using
      setupHeap_slots (base q full capWords bits) ((prepareNormalization q full).indexed.children.get node).size
        (bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) initial hw
  · intro child hc
    rw [hh]
    exact setupHeap_outside _ _ _ initial hw _
      ((show countsBase + child ≤ countsBase + (prepareNormalization q full).indexed.nodes.size by omega).trans_lt hfit)
      (by omega)
  · intro physical hp hout
    rw [hh]
    exact setupHeap_outside _ _ _ initial hw physical hp hout
  · omega
  · rw [executeOps_halted, ha]

theorem degree_fits {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits)
    (node : (prepareNormalization q full).indexed.NodeId) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap) :
    Fits bits ((prepareNormalization q full).indexed.children.get node).size := by
  have hw := degree_word full configuration capWords heap hq rep node
  have hn := chunk_toNat full configuration capWords heap hq rep 2 node.val (by decide) (by simp [chunks])
  have hn' : (heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 2 + node.val)))).toNat =
      ((prepareNormalization q full).indexed.children.get node).size := by
    simpa [chunks, mapped_finRange_get] using hn
  rw [hw, BitVec.toNat_ofNat] at hn'
  unfold Fits
  rw [← hn']
  exact Nat.mod_lt _ (Nat.two_pow_pos bits)

theorem body_data {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords countsBase offset origin count : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (initial state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hN : Fits bits full.length)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7))
    (hbase : base q full capWords bits + 16 ≤ countsBase)
    (hfit : Fits bits (countsBase + (prepareNormalization q full).indexed.nodes.size))
    (hbreg : initial.register .old = BitVec.ofNat bits countsBase)
    (horeg : initial.register .fresh = BitVec.ofNat bits offset)
    (hoff : offset + ((prepareNormalization q full).indexed.children.get node).size ≤ edgeCount q full)
    (hc : count < ((prepareNormalization q full).indexed.children.get node).size)
    (data : LoopData full configuration capWords countsBase offset node initial count state) :
    LoopData full configuration capWords countsBase offset node initial (count + 1)
      (executeOps (callInput q full command) (bodyLead origin) state) := by
  let workspace := base q full capWords bits
  let degree := ((prepareNormalization q full).indexed.children.get node).size
  let internal := bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)
  let total := prefixSum full initial.heap countsBase offset count
  let child := (PSTRStaticLayout.childWords q full).getD (offset + count) 0
  let value := (initial.heap (BitVec.ofNat bits (countsBase + child))).toNat
  have hchild : child < (prepareNormalization q full).indexed.nodes.size := child_id_lt full _ (by omega)
  have hvalue : (state.heap (BitVec.ofNat bits (countsBase + child))).toNat = value := by rw [data.array child hchild]
  dsimp only [child] at hvalue
  have h0 : state.heap (BitVec.ofNat bits workspace) = BitVec.ofNat bits countsBase := by
    simpa only [slotValue, Nat.add_zero, hbreg] using data.slots 0 (by decide)
  have h1 : state.heap (BitVec.ofNat bits (workspace + 1)) = BitVec.ofNat bits offset := by
    simpa only [slotValue, horeg] using data.slots 1 (by decide)
  have h6 : state.heap (BitVec.ofNat bits (workspace + 6)) = BitVec.ofNat bits count := by
    simpa only [slotValue] using data.slots 6 (by decide)
  have h7 : state.heap (BitVec.ofNat bits (workspace + 7)) = BitVec.ofNat bits total := by
    simpa only [slotValue] using data.slots 7 (by decide)
  have hex := execute_bodyLead full command configuration capWords origin countsBase offset count total state
    hb hq data.rep hN hw (by omega) h0 h1 h6 h7
  have hh : (executeOps (callInput q full command) (bodyLead origin) state).heap =
      Function.update (Function.update state.heap (BitVec.ofNat bits (workspace + 7)) (BitVec.ofNat bits (total + value)))
        (BitVec.ofNat bits (workspace + 6)) (BitVec.ofNat bits (count + 1)) := by
    simpa only [hvalue] using hex.1
  have hw3 : Fits bits (workspace + 3) := (show workspace + 3 ≤ workspace + 7 by omega).trans_lt hw
  constructor
  · rw [hh]
    have r7 := scratch_store_represents full configuration capWords (workspace + 7) state.heap
      (BitVec.ofNat bits (total + value)) (by omega) hq data.rep bitmap hr hw3 hw (by omega)
    exact scratch_store_represents full configuration capWords (workspace + 6) _
      (BitVec.ofNat bits (count + 1)) (by omega) hq r7 bitmap hr hw3
      ((show workspace + 6 ≤ workspace + 7 by omega).trans_lt hw) (by omega)
  · rw [hh]
    have hs := slots_after_accumulate workspace degree internal count total value initial state.heap hw data.slots
    simpa only [prefixSum_succ] using hs
  · intro other ho
    rw [hh,
      workspace_store_counts_frame _ workspace countsBase other 6 _ hbase (by decide)
        ((show countsBase + other ≤ countsBase + (prepareNormalization q full).indexed.nodes.size by omega).trans_lt hfit),
      workspace_store_counts_frame _ workspace countsBase other 7 _ hbase (by decide)
        ((show countsBase + other ≤ countsBase + (prepareNormalization q full).indexed.nodes.size by omega).trans_lt hfit),
      data.array other ho]
  · intro physical hp hout
    rw [hh,
      store_other _ (workspace + 6) physical _ ((show workspace + 6 ≤ workspace + 7 by omega).trans_lt hw) hp (by omega),
      store_other _ (workspace + 7) physical _ hw hp (by omega)]
    exact data.outside physical hp hout
  · omega
  · rw [executeOps_halted, data.active]

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
