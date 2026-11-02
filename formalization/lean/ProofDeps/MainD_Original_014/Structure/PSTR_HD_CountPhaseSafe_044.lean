module

public import Structure.PSTR_HD_CountPrefixFetch_043

/-! Access and frame certificates for each actually executed loop phase.
The real cached child ID determines the physical counts read. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRCountWorkspace PSTRStaticLayout

theorem testLead_prefixOK {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords countsBase node heapWords origin : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : base q full capWords bits + 7 < heapWords) :
    PrefixOK (callInput q full command) heapWords
      (nodeProtected (base q full capWords bits) countsBase node) (testLead origin) state := by
  have hl := execute_base full command configuration capWords state hb hq rep
  rw [testLead_split]
  apply prefixOK_append
  · exact locator_prefixOK full command configuration capWords countsBase node heapWords state hb rep (by omega)
  · apply readOnly_prefixOK _ _ _ _ _ (testOps_readOnly origin)
    exact testOps_prefix_access _ origin _ heapWords _ hl.1 hroom

theorem bodyLead_prefixOK {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords countsBase offset count heapWords origin : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (initial state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hN : Fits bits full.length)
    (hw : Fits bits (base q full capWords bits + 7))
    (hroom : base q full capWords bits + 7 < heapWords)
    (hcounts : countsBase + (prepareNormalization q full).indexed.nodes.size ≤ heapWords)
    (hbreg : initial.register .old = BitVec.ofNat bits countsBase)
    (horeg : initial.register .fresh = BitVec.ofNat bits offset)
    (hoff : offset + ((prepareNormalization q full).indexed.children.get node).size ≤ edgeCount q full)
    (hc : count < ((prepareNormalization q full).indexed.children.get node).size)
    (data : LoopData full configuration capWords countsBase offset node initial count state) :
    PrefixOK (callInput q full command) heapWords
      (nodeProtected (base q full capWords bits) countsBase node.val) (bodyLead origin) state := by
  let rom := callInput q full command
  let workspace := base q full capWords bits
  let region := nodeProtected workspace countsBase node.val
  let s0 := executeOps rom PSTRCountWorkspace.program state
  have h0 := execute_base full command configuration capWords state hb hq data.rep
  have p0 := locator_prefixOK full command configuration capWords countsBase node.val heapWords state hb data.rep (by omega)
  have p1 : PrefixOK rom heapWords region childPosition s0 := by
    apply readOnly_prefixOK _ _ _ _ _ childPosition_readOnly
    exact childPosition_prefix_access rom workspace heapWords s0 h0.1 hroom
  have ho : s0.heap (BitVec.ofNat bits (workspace + 1)) = BitVec.ofNat bits offset := by
    rw [h0.2.2.2.2.2.1]
    simpa only [slotValue, horeg] using data.slots 1 (by decide)
  have hk : s0.heap (BitVec.ofNat bits (workspace + 6)) = BitVec.ofNat bits count := by
    rw [h0.2.2.2.2.2.1]
    simpa only [slotValue] using data.slots 6 (by decide)
  let s1 := executeOps rom childPosition s0
  have h1 := execute_childPosition rom workspace offset count s0 h0.1 ho hk
  have r1 : HeapRepresents q full capWords configuration s1.heap := by
    rw [h1.2, h0.2.2.2.2.2.1]
    exact data.rep
  have hp : offset + count < edgeCount q full := by omega
  have p2 := fields_prefixOK full command configuration capWords countsBase node.val heapWords s1 ⟨3, by decide⟩
    (offset + count) hb hq r1 hN hp h1.1 (by omega)
  let s2 := executeOps rom (PSTRStaticFields.program ⟨3, by decide⟩) s1
  have h2 := PSTRStaticFields.execute_field full command configuration capWords s1 ⟨3, by decide⟩
    (offset + count) hb hq r1 hN hp h1.1
  have hv : s2.register .value = BitVec.ofNat bits ((PSTRStaticLayout.childWords q full).getD (offset + count) 0) := by
    have hv := h2.1
    change s2.register .value = BitVec.ofNat bits ((PSTRStaticLayout.childWords q full)[offset + count]) at hv
    rw [List.getD_eq_getElem _ _ hp]
    exact hv
  have r2 : HeapRepresents q full capWords configuration s2.heap := by rw [h2.2.2.2]; exact r1
  have p3 := locator_prefixOK full command configuration capWords countsBase node.val heapWords s2 hb r2 (by omega)
  let s3 := executeOps rom PSTRCountWorkspace.program s2
  have h3 := execute_base full command configuration capWords s2 hb hq r2
  have hh : s3.heap = state.heap := h3.2.2.2.2.2.1.trans (h2.2.2.2.trans (h1.2.trans h0.2.2.2.2.2.1))
  have p4 := accumulate_prefixOK rom workspace countsBase node.val
    ((PSTRStaticLayout.childWords q full).getD (offset + count) 0) heapWords origin s3 h3.1 (h3.2.1.trans hv)
    (by rw [hh]; simpa only [slotValue, Nat.add_zero, hbreg] using data.slots 0 (by decide)) hw hroom
    (by have hi := child_id_lt full (offset + count) hp; omega)
  have c1 := prefixOK_append rom heapWords region PSTRCountWorkspace.program childPosition state p0 p1
  have c2 := prefixOK_append rom heapWords region (PSTRCountWorkspace.program ++ childPosition)
    (PSTRStaticFields.program ⟨3, by decide⟩) state c1 (by simpa only [executeOps_append] using p2)
  have c3 := prefixOK_append rom heapWords region (PSTRCountWorkspace.program ++ childPosition ++ PSTRStaticFields.program ⟨3, by decide⟩)
    PSTRCountWorkspace.program state c2 (by simpa only [executeOps_append] using p3)
  exact prefixOK_append rom heapWords region
    (PSTRCountWorkspace.program ++ childPosition ++ PSTRStaticFields.program ⟨3, by decide⟩ ++ PSTRCountWorkspace.program)
    (accumulate origin) state c3 (by simpa only [executeOps_append] using p4)

theorem footer_prefixOK {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords countsBase offset count heapWords : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (initial state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (hfit : Fits bits (countsBase + node.val))
    (hroom : base q full capWords bits + 7 < heapWords) (hnode : countsBase + node.val < heapWords)
    (hbreg : initial.register .old = BitVec.ofNat bits countsBase)
    (hireg : initial.register .index = BitVec.ofNat bits node.val)
    (data : LoopData full configuration capWords countsBase offset node initial count state) :
    PrefixOK (callInput q full command) heapWords
      (nodeProtected (base q full capWords bits) countsBase node.val) footer state := by
  have hl := execute_base full command configuration capWords state hb hq data.rep
  apply prefixOK_append
  · exact locator_prefixOK full command configuration capWords countsBase node.val heapWords state hb data.rep (by omega)
  · apply finishStores_prefixOK _ _ _ _ heapWords _ hl.1
    · rw [hl.2.2.2.2.2.1]
      simpa only [slotValue, Nat.add_zero, hbreg] using data.slots 0 (by decide)
    · rw [hl.2.2.2.2.2.1]
      simpa only [slotValue, hireg] using data.slots 2 (by decide)
    · exact hfit
    · exact hroom
    · exact hnode

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
