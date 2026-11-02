module

public import PaperProofs.Structure.PSTR_HD_CountRefines_049

/-! Actual final workspace words for the caller's next-node advance. The
footer's single counts store preserves all eight real W slots. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRWordSegments PSTRCountWorkspace PSTRStaticLayout PSTRCountBounds

section Slots

variable {bits q : Nat} (full : List (Finset (Fin q))) (command : Command) (configuration : Configuration q)
    (capWords countsBase offset origin leaf : Nat) (node : (prepareNormalization q full).indexed.NodeId)
    (initial : WordState bits) (containing : List PackingOp)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length),
      containing[origin + i]'(kernel_index_bound containing origin hbound i hi) = (programAt origin)[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (hb : 8 ≤ bits) (hq : 0 < q) (hN : Fits bits full.length)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7))
    (hbase : base q full capWords bits + 16 ≤ countsBase)
    (hfit : Fits bits (countsBase + (prepareNormalization q full).indexed.nodes.size))
    (hbreg : initial.register .old = BitVec.ofNat bits countsBase)
    (horeg : initial.register .fresh = BitVec.ofNat bits offset)
    (hireg : initial.register .index = BitVec.ofNat bits node.val)
    (hlreg : initial.register .value = BitVec.ofNat bits leaf)
    (hoff : offset + ((prepareNormalization q full).indexed.children.get node).size ≤ edgeCount q full)

include hbound hcode hwords hpcfit hb hq hN bitmap hr hw hbase hfit hbreg horeg hireg hlreg hoff

theorem active_node_slots
    (rep : HeapRepresents q full capWords configuration initial.heap)
    (hp : initial.pc = BitVec.ofNat bits (5 * origin)) (ha : initial.halted = false) :
    let degree := ((prepareNormalization q full).indexed.children.get node).size
    HasSlots (base q full capWords bits) degree
      (bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) degree
      (prefixSum full initial.heap countsBase offset degree) initial
      (packingRun (callInput q full command) containing (activeSteps degree) initial).heap := by
  dsimp only
  let rom := callInput q full command
  let degree := ((prepareNormalization q full).indexed.children.get node).size
  let started := packingRun rom containing 121 initial
  have hs := fetched_setup_ready full command configuration capWords countsBase offset origin node initial
    containing hbound hcode hwords hpcfit hb hq hN bitmap hr hw hbase hfit rep hireg hp ha
  let looped := packingRun rom containing (114 * degree) started
  have hl := fetched_iterations full command configuration capWords countsBase offset origin node initial
    containing hbound hcode hwords hpcfit hb hq hN bitmap hr hw hbase hfit hbreg horeg hoff
    0 degree started (by omega) hs
  simp only [Nat.zero_add] at hl
  let tested := packingRun rom containing 28 looped
  have ht := fetched_test_state full command configuration capWords countsBase offset origin node initial
    containing hbound hcode hwords hpcfit hb hq degree looped hl
  have htp : tested.pc = BitVec.ofNat bits (5 * (origin + 235)) := by rw [ht.2, ite_eq_left rfl]
  have hf := fetched_finish full command configuration capWords countsBase offset origin leaf node initial
    containing hbound hcode hwords hpcfit hb hq bitmap hr hw hbase hfit hbreg hireg hlreg tested ht.1 htp
  dsimp only at hf
  rw [show activeSteps degree = 121 + (114 * degree + (28 + 35)) by unfold activeSteps; omega,
    run_add, run_add, run_add]
  intro slot hslot
  have hfnode : Fits bits (countsBase + node.val) :=
    (show countsBase + node.val ≤ countsBase + (prepareNormalization q full).indexed.nodes.size by have hn := node.isLt; omega).trans_lt hfit
  have hfslot : Fits bits (base q full capWords bits + slot) :=
    (show base q full capWords bits + slot ≤ base q full capWords bits + 7 by omega).trans_lt hw
  rw [hf.1, store_other _ (countsBase + node.val) (base q full capWords bits + slot) _ hfnode hfslot (by omega)]
  exact ht.1.slots slot hslot

theorem active_node_degree
    (rep : HeapRepresents q full capWords configuration initial.heap)
    (hp : initial.pc = BitVec.ofNat bits (5 * origin)) (ha : initial.halted = false) :
    let degree := ((prepareNormalization q full).indexed.children.get node).size
    (packingRun (callInput q full command) containing (activeSteps degree) initial).heap
      (BitVec.ofNat bits (base q full capWords bits + 4)) = BitVec.ofNat bits degree := by
  have hs := active_node_slots full command configuration capWords countsBase offset origin leaf node initial containing
    hbound hcode hwords hpcfit hb hq hN bitmap hr hw hbase hfit hbreg horeg hireg hlreg hoff rep hp ha
  simpa only [slotValue] using hs 4 (by decide)

end Slots

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
