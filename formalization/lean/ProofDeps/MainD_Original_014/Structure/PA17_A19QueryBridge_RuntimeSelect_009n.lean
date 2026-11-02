module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009m
public import Structure.PA17_A19QueryBridge_RuntimeSelect_009g

/-! Real access certificates for the packed-read/push and reverse body.
The particular runtime source cells and allocated addresses suffice; an
all-prefix NumericSafe/Access oracle is not an input of these theorems. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem pushProgram_address {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom pushProgram state).register .address = state.register .address := rfl

theorem reverseBody_readPush (origin : Nat) : reverseBody origin = readPushProgram ++ reverseFoot origin := by
  simp only [reverseBody, reverseBodyLead, readPushProgram, reverseFoot, List.append_assoc]

theorem reverseBody_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords origin header base candidates counts parents node parent : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hheader : header = PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
    (hheaderAlloc : header + 12 < heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (h1 : Fits bits 1) (hn : Fits bits (node + 1))
    (hptr : Fits bits (base + node)) (hscalar : base + node < capWords)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hbase : state.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits base)
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits candidates)
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent)
    (hcountAlloc : counts + node < heapWords) (hparentAlloc : parents + (node + 1) < heapWords)
    (hcandidateAlloc : candidates + parent < heapWords) :
    ∀ clock (hc : clock < (reverseBody origin).length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) ((reverseBody origin).take clock) state) (reverseBody origin)[clock] := by
  let rom := callInput q full command
  let located := executeOps rom payloadRead state
  let loaded := executeOps rom PA17A19RuntimeRead007.cachedProgram located
  have hl := payloadRead_result rom header base node state h1 hn hh hnode hbase
  have hlrep : HeapRepresents q full capWords configuration located.heap := by rw [hl.2.2]; exact rep
  have hscalarWord : (located.register .value).toNat < capWords := by
    rw [hl.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hptr]
    exact hscalar
  have hreader := PA17A19RuntimeRead007.execute_cached full command configuration capWords heapWords located hb hq hw hlrep
    hscalarWord hs hf (by rw [← hheader]; omega)
    (by rw [hl.2.2]; exact hwidth) (by rw [hl.2.2]; exact hmask)
    (by simpa only [← hheader] using hl.1)
  have hm : loaded.heap = state.heap := hreader.2.2.1.trans hl.2.2
  have had : loaded.register .address = BitVec.ofNat bits header := by simpa only [← hheader] using hreader.1
  have hloadAccess := PA17A19RuntimeRead007.cached_access_prefix full command configuration capWords heapWords located hb hq hw
    hlrep hscalarWord hs hf (by rw [← hheader]; omega)
    (by rw [hl.2.2]; exact hwidth) (by simpa only [← hheader] using hl.1)
  have hprefix := PA17A19RuntimeRead007.access_append rom heapWords payloadRead PA17A19RuntimeRead007.cachedProgram state
    (payloadRead_access rom header heapWords state hh (by omega)) hloadAccess
  have hpushAccess : ∀ clock (hc : clock < pushProgram.length), packingAccessFits rom heapWords
      (executeOps rom (pushProgram.take clock) loaded) pushProgram[clock] := by
    intro clock hc
    exact pushProgram_access rom header candidates counts parents node parent heapWords loaded h1 hn had
      (by rw [hm]; exact hnode) (by rw [hm]; exact hcandidates) (by rw [hm]; exact hcounts)
      (by rw [hm]; exact hparents) (by rw [hm]; exact hreadParent)
      hheaderAlloc hcountAlloc hparentAlloc hcandidateAlloc clock hc
  have hreadPushAccess : ∀ clock (hc : clock < readPushProgram.length), packingAccessFits rom heapWords
      (executeOps rom (readPushProgram.take clock) state) readPushProgram[clock] := by
    simpa only [readPushProgram, executeOps_append] using
      PA17A19RuntimeRead007.access_append rom heapWords (payloadRead ++ PA17A19RuntimeRead007.cachedProgram) pushProgram state
        hprefix (by simpa only [executeOps_append] using hpushAccess)
  have hfinishHeader : (executeOps rom readPushProgram state).register .address = BitVec.ofNat bits header := by
    rw [readPushProgram, executeOps_append, pushProgram_address]
    exact had
  rw [reverseBody_readPush]
  exact PA17A19RuntimeRead007.access_append rom heapWords readPushProgram (reverseFoot origin) state hreadPushAccess
    (reverseFoot_access rom origin header heapWords _ hfinishHeader (by omega))

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
