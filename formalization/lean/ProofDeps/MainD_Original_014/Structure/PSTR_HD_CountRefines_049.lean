module

public import Structure.PSTR_HD_CountCost_048

/-! Instantiate the actual physical-array kernel with the ORIGINAL
usedCounts/countNode specification and its real leaf producer register. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRWordSegments PSTRCountWorkspace PSTRStaticLayout PSTRCountBounds
open IndexedUsedCounts IndexedDescent

theorem active_node_usedCount {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords countsBase offset origin : Nat) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId) (initial : WordState bits) (containing : List PackingOp)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(kernel_index_bound containing origin hbound i hi) = (programAt origin)[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (hb : 8 ≤ bits) (hq : 0 < q) (hl : LaminarSchedule full) (hN : Fits bits full.length) (hqfit : Fits bits q)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7))
    (hbase : base q full capWords bits + 16 ≤ countsBase)
    (hfit : Fits bits (countsBase + (prepareNormalization q full).indexed.nodes.size))
    (hbreg : initial.register .old = BitVec.ofNat bits countsBase)
    (horeg : initial.register .fresh = BitVec.ofNat bits offset)
    (hireg : initial.register .index = BitVec.ofNat bits node.val)
    (hlreg : initial.register .value = BitVec.ofNat bits ((leafBitmap (prepareNormalization q full).indexed used).get node))
    (hoff : offset + ((prepareNormalization q full).indexed.children.get node).size ≤ edgeCount q full)
    (row : ∀ position (hp : position < ((prepareNormalization q full).indexed.children.get node).size),
      (PSTRStaticLayout.childWords q full).getD (offset + position) 0 =
        (((prepareNormalization q full).indexed.children.get node)[position]).val)
    (previous : ∀ child : (prepareNormalization q full).indexed.NodeId, child.val < node.val →
      initial.heap (BitVec.ofNat bits (countsBase + child.val)) =
        BitVec.ofNat bits ((usedCounts (prepareNormalization q full).indexed used).get child))
    (rep : HeapRepresents q full capWords configuration initial.heap)
    (hp : initial.pc = BitVec.ofNat bits (5 * origin)) (ha : initial.halted = false) :
    let result := packingRun (callInput q full command) containing
      (activeSteps ((prepareNormalization q full).indexed.children.get node).size) initial
    let expected := (usedCounts (prepareNormalization q full).indexed used).get node
    result.halted = false ∧ result.pc = BitVec.ofNat bits (5 * (origin + 270)) ∧
      result.register .value = BitVec.ofNat bits expected ∧
      result.register .address = BitVec.ofNat bits (countsBase + node.val) ∧
      result.register .index = BitVec.ofNat bits node.val ∧
      HeapRepresents q full capWords configuration result.heap ∧
      (∀ child < (prepareNormalization q full).indexed.nodes.size,
        result.heap (BitVec.ofNat bits (countsBase + child)) =
          if child = node.val then BitVec.ofNat bits expected else initial.heap (BitVec.ofNat bits (countsBase + child))) ∧
      (∀ physical, Fits bits physical →
        (physical < base q full capWords bits ∨ base q full capWords bits + 8 ≤ physical) →
        physical ≠ countsBase + node.val →
        result.heap (BitVec.ofNat bits physical) = initial.heap (BitVec.ofNat bits physical)) := by
  have h := active_node_run full command configuration capWords countsBase offset origin
    ((leafBitmap (prepareNormalization q full).indexed used).get node) node initial containing hbound hcode hwords hpcfit
    hb hq hN bitmap hr hw hbase hfit hbreg horeg hireg hlreg hoff rep hp ha
  have hs := PSTRCountSpec.nodeResult_eq_usedCount full used node initial.heap countsBase offset hq hl hqfit row previous
  simp only [PSTRCountSpec.nodeResult] at hs
  simpa only [hs] using h

theorem halt_at_exit {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (count : Nat) (initial : WordState bits) (hwords : WordsFit bits (packingCode containing))
    (hfit : Fits bits (5 * containing.length))
    (ha : (packingRun rom containing count initial).halted = false)
    (hp : (packingRun rom containing count initial).pc = BitVec.ofNat bits (5 * containing.length)) :
    packingRun rom containing (count + 1) initial = { packingRun rom containing count initial with halted := true } := by
  rw [run_add]
  change packingStep rom ((packingCode containing).map (BitVec.ofNat bits)) _ = _
  exact packingStep_halt rom containing _ hwords
    (by rw [hp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hfit) ha

theorem original_partial_sum_fit {q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (countsBase offset count : Nat) (hq : 0 < q) (hl : LaminarSchedule full)
    (hqfit : Fits (indexWidth 32 full.length q) q)
    (hc : count ≤ ((prepareNormalization q full).indexed.children.get node).size)
    (hoff : offset + ((prepareNormalization q full).indexed.children.get node).size ≤ edgeCount q full)
    (row : ∀ position (hp : position < ((prepareNormalization q full).indexed.children.get node).size),
      (PSTRStaticLayout.childWords q full).getD (offset + position) 0 =
        (((prepareNormalization q full).indexed.children.get node)[position]).val)
    (previous : ∀ child : (prepareNormalization q full).indexed.NodeId, child.val < node.val →
      heap (BitVec.ofNat (indexWidth 32 full.length q) (countsBase + child.val)) =
        BitVec.ofNat (indexWidth 32 full.length q) ((usedCounts (prepareNormalization q full).indexed used).get child)) :
    Fits (indexWidth 32 full.length q) (prefixSum full heap countsBase offset count) := by
  apply PSTRCountBounds.original_partial_sum_fit full heap countsBase offset count
  · have he := edgeCount_eq q full hq hl
    omega
  · intro position hp
    have hpos : position < ((prepareNormalization q full).indexed.children.get node).size := by omega
    rw [row position hpos]
    let child := ((prepareNormalization q full).indexed.children.get node)[position]
    have hbefore : child.val < node.val :=
      prepared_child_index_lt q full hq hl node child (Array.getElem_mem_toList hpos)
    rw [previous child hbefore, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ((usedCount_bound (prepareNormalization q full).indexed used child).trans_lt hqfit)]
    exact usedCount_bound (prepareNormalization q full).indexed used child

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
