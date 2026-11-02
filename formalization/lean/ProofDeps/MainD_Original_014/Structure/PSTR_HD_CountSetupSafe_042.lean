module

public import Structure.PSTR_HD_CountSafeBlocks_041

/-! Every actual setup prefix is memory-safe and protects the original
heap metadata/capacity prefix, caller workspace and the physical counts array. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRCountWorkspace PSTRStaticLayout

theorem setup_prefixOK {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords countsBase heapWords : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (initial : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration initial.heap)
    (hN : Fits bits full.length) (hi : initial.register .index = BitVec.ofNat bits node.val)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7))
    (hroom : base q full capWords bits + 7 < heapWords) :
    PrefixOK (callInput q full command) heapWords
      (nodeProtected (base q full capWords bits) countsBase node.val) setup initial := by
  let rom := callInput q full command
  let workspace := base q full capWords bits
  let region := nodeProtected workspace countsBase node.val
  have hw3 : Fits bits (workspace + 3) := (show workspace + 3 ≤ workspace + 7 by omega).trans_lt hw
  let loc0 := executeOps rom PSTRCountWorkspace.program initial
  have hl0 := execute_base full command configuration capWords initial hb hq rep
  have pl0 := locator_prefixOK full command configuration capWords countsBase node.val heapWords initial hb rep (by omega)
  have psp := spill_prefixOK rom workspace countsBase node.val heapWords loc0 hl0.1 hw hroom
  have pb : PrefixOK rom heapWords region bootstrap initial :=
    prefixOK_append rom heapWords region PSTRCountWorkspace.program spillProgram initial pl0 psp
  let s0 := executeOps rom bootstrap initial
  have h0 := execute_bootstrap full command configuration capWords initial hb hq rep
  have r0 : HeapRepresents q full capWords configuration s0.heap := by
    rw [h0.1]
    exact entry_represents full configuration capWords initial (by omega) hq rep bitmap hr hw3
  have i0 : s0.register .index = BitVec.ofNat bits node.val := h0.2.2.2.1.trans hi
  have p1 := fields_prefixOK full command configuration capWords countsBase node.val heapWords s0 ⟨2, by decide⟩ node.val
    hb hq r0 hN (by simp [chunks]) i0 (by omega)
  let s1 := executeOps rom (PSTRStaticFields.program ⟨2, by decide⟩) s0
  have h1 := PSTRStaticFields.execute_field full command configuration capWords s0 ⟨2, by decide⟩ node.val hb hq r0 hN
    (by simp [chunks]) i0
  have r1 : HeapRepresents q full capWords configuration s1.heap := by rw [h1.2.2.2]; exact r0
  have i1 : s1.register .index = BitVec.ofNat bits node.val := h1.2.2.1.trans i0
  have p2 := locator_prefixOK full command configuration capWords countsBase node.val heapWords s1 hb r1 (by omega)
  let s2 := executeOps rom PSTRCountWorkspace.program s1
  have h2 := execute_base full command configuration capWords s1 hb hq r1
  have r2 : HeapRepresents q full capWords configuration s2.heap := by rw [h2.2.2.2.2.2.1]; exact r1
  have i2 : s2.register .index = BitVec.ofNat bits node.val := h2.2.2.1.trans i1
  have p3 := saveField_prefixOK rom workspace countsBase node.val heapWords 4 s2 h2.1 hw (by decide) hroom
  let s3 := executeOps rom (saveField 4) s2
  have h3 := execute_saveField rom 4 workspace s2 h2.1
  have r3 : HeapRepresents q full capWords configuration s3.heap := by
    rw [h3.1]
    exact scratch_store_represents full configuration capWords (workspace + 4) s2.heap (s2.register .value)
      (by omega) hq r2 bitmap hr hw3 ((show workspace + 4 ≤ workspace + 7 by omega).trans_lt hw) (by omega)
  have i3 : s3.register .index = BitVec.ofNat bits node.val := h3.2.2.trans i2
  have p4 := fields_prefixOK full command configuration capWords countsBase node.val heapWords s3 ⟨5, by decide⟩ node.val
    hb hq r3 hN (by simp [chunks]) i3 (by omega)
  let s4 := executeOps rom (PSTRStaticFields.program ⟨5, by decide⟩) s3
  have h4 := PSTRStaticFields.execute_field full command configuration capWords s3 ⟨5, by decide⟩ node.val hb hq r3 hN
    (by simp [chunks]) i3
  have r4 : HeapRepresents q full capWords configuration s4.heap := by rw [h4.2.2.2]; exact r3
  have p5 := locator_prefixOK full command configuration capWords countsBase node.val heapWords s4 hb r4 (by omega)
  let s5 := executeOps rom PSTRCountWorkspace.program s4
  have h5 := execute_base full command configuration capWords s4 hb hq r4
  have p6 := saveField_prefixOK rom workspace countsBase node.val heapWords 5 s5 h5.1 hw (by decide) hroom
  let s6 := executeOps rom (saveField 5) s5
  have h6 := execute_saveField rom 5 workspace s5 h5.1
  have p7 := clearLoop_prefixOK rom workspace countsBase node.val heapWords s6 h6.2.1 hw hroom
  have c1 := prefixOK_append rom heapWords region bootstrap (PSTRStaticFields.program ⟨2, by decide⟩) initial pb p1
  have c2 := prefixOK_append rom heapWords region (bootstrap ++ PSTRStaticFields.program ⟨2, by decide⟩)
    PSTRCountWorkspace.program initial c1 (by simpa only [executeOps_append] using p2)
  have c3 := prefixOK_append rom heapWords region
    (bootstrap ++ PSTRStaticFields.program ⟨2, by decide⟩ ++ PSTRCountWorkspace.program)
    (saveField 4) initial c2 (by simpa only [executeOps_append] using p3)
  have c4 := prefixOK_append rom heapWords region
    (bootstrap ++ PSTRStaticFields.program ⟨2, by decide⟩ ++ PSTRCountWorkspace.program ++ saveField 4)
    (PSTRStaticFields.program ⟨5, by decide⟩) initial c3 (by simpa only [executeOps_append] using p4)
  have c5 := prefixOK_append rom heapWords region
    (bootstrap ++ PSTRStaticFields.program ⟨2, by decide⟩ ++ PSTRCountWorkspace.program ++ saveField 4 ++ PSTRStaticFields.program ⟨5, by decide⟩)
    PSTRCountWorkspace.program initial c4 (by simpa only [executeOps_append] using p5)
  have c6 := prefixOK_append rom heapWords region
    (bootstrap ++ PSTRStaticFields.program ⟨2, by decide⟩ ++ PSTRCountWorkspace.program ++ saveField 4 ++ PSTRStaticFields.program ⟨5, by decide⟩ ++ PSTRCountWorkspace.program)
    (saveField 5) initial c5 (by simpa only [executeOps_append] using p6)
  exact prefixOK_append rom heapWords region
    (bootstrap ++ PSTRStaticFields.program ⟨2, by decide⟩ ++ PSTRCountWorkspace.program ++ saveField 4 ++ PSTRStaticFields.program ⟨5, by decide⟩ ++ PSTRCountWorkspace.program ++ saveField 5)
    clearLoop initial c6 (by simpa only [executeOps_append] using p7)

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
