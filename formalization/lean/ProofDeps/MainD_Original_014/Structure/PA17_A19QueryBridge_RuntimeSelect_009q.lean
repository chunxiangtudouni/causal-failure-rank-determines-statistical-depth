module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009p

/-! HD's entire exclusive suffix is framed through every real instruction
of a packed-read reverse105 iteration, including both executed jumps. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem reverseBody_prefixFrame {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords origin header base candidates counts parents node parent : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hheader : header = PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
    (hheaderAlloc : header < heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (h1 : Fits bits 1) (hn : Fits bits (node + 1)) (hparent : Fits bits parent)
    (hptr : Fits bits (base + node)) (hscalar : base + node < capWords)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hbase : state.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits base)
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits candidates)
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent)
    (address : BitVec bits) (hneHeader : address ≠ BitVec.ofNat bits (header + 8))
    (hneCandidate : address ≠ BitVec.ofNat bits (candidates + parent)) :
    WordPrefixFrame (callInput q full command) (reverseBody origin) state address := by
  let rom := callInput q full command
  let located := executeOps rom payloadRead state
  let loaded := executeOps rom PA17A19RuntimeRead007.cachedProgram located
  have hl := payloadRead_result rom header base node state h1 hn hh hnode hbase
  have hlrep : HeapRepresents q full capWords configuration located.heap := by rw [hl.2.2]; exact rep
  have hreader := PA17A19RuntimeRead007.execute_cached full command configuration capWords heapWords located hb hq hw hlrep
    (by rw [hl.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hptr]; exact hscalar) hs hf
    (by simpa only [← hheader] using hheaderAlloc)
    (by rw [hl.2.2]; exact hwidth) (by rw [hl.2.2]; exact hmask)
    (by simpa only [← hheader] using hl.1)
  have hm : loaded.heap = state.heap := hreader.2.2.1.trans hl.2.2
  have had : loaded.register .address = BitVec.ofNat bits header := by simpa only [← hheader] using hreader.1
  have hpush := pushProgram_prefixFrame_cells rom header candidates counts parents node parent loaded h1 hn hparent had
    (by rw [hm]; exact hnode) (by rw [hm]; exact hcandidates) (by rw [hm]; exact hcounts)
    (by rw [hm]; exact hparents) (by rw [hm]; exact hreadParent) address hneCandidate
  have hprefix := WordPrefixFrame.append rom payloadRead PA17A19RuntimeRead007.cachedProgram state address
    (WordPrefixFrame.noStore rom payloadRead state address payloadRead_noStore)
    (WordPrefixFrame.noStore rom PA17A19RuntimeRead007.cachedProgram located address PA17A19RuntimeRead007.cachedProgram_noStore)
  have hreadPush : WordPrefixFrame rom readPushProgram state address := by
    simpa only [readPushProgram, executeOps_append] using
      WordPrefixFrame.append rom (payloadRead ++ PA17A19RuntimeRead007.cachedProgram) pushProgram state address hprefix
        (by simpa only [executeOps_append] using hpush)
  have hadEnd : (executeOps rom readPushProgram state).register .address = BitVec.ofNat bits header := by
    rw [readPushProgram, executeOps_append, pushProgram_address]
    exact had
  rw [reverseBody_readPush]
  exact WordPrefixFrame.append rom readPushProgram (reverseFoot origin) state address hreadPush
    (reverseFoot_prefixFrame rom origin header _ hadEnd address hneHeader)

theorem actual_reverse_suffix_frame {bits q origin : Nat} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords header base counts parents node parent size : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hheader : header = PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
    (hheaderAlloc : header < heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (h1 : Fits bits 1) (hn : Fits bits (node + 1)) (hparent : Fits bits parent)
    (hptr : Fits bits (base + node)) (hscalar : base + node < capWords)
    (hroom : Fits bits (endpoint header q size)) (hparentBound : parent ≤ size)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hbase : state.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits base)
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (childBase header q))
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent)
    (clock : Nat) (hc : clock ≤ 105) (physical : Nat) (hphysical : Fits bits physical)
    (hsuffix : endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  let rom := callInput q full command
  let tested := executeOps rom (reverseTest origin) state
  by_cases htest : clock ≤ 5
  · have hbound : origin + (reverseTest origin).length ≤ containing.length := by
      have hh := em.bound; rw [reverseTest_length, reverseProgramAt_length] at *; omega
    rw [PA17A19RuntimeRanks008.last_prefix rom containing (reverseTestLead origin) (.jumpIfZero .total .old) origin hbound
      (reverse_test_code em) (reverseTestLead_straight origin) em.words em.pcfit state hp ha clock (by rw [reverseTestLead_length]; omega)]
    exact WordPrefixFrame.noStore rom (reverseTest origin) state _ (reverseTest_noStore origin) clock
      (by rwa [reverseTest_length])
  · have ht := reverseTest_result rom origin header (node + 1) state hn hh hp hnode
    have htestpc : tested.pc = BitVec.ofNat bits (5 * (origin + 5)) := by
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
    have htestrep : HeapRepresents q full capWords configuration tested.heap := by rw [ht.2.2]; exact rep
    have hfitH8 : Fits bits (header + 8) := by
      apply (show header + 8 ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt hroom
    have hfitTarget : Fits bits (childBase header q + parent) :=
      (show childBase header q + parent ≤ endpoint header q size by unfold endpoint; omega).trans_lt hroom
    have hneH8 : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (header + 8) := by
      apply (ofNat_injective_of_fit _ _ hphysical hfitH8).not.mpr
      unfold endpoint childBase at hsuffix
      omega
    have hneTarget : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (childBase header q + parent) := by
      apply (ofNat_injective_of_fit _ _ hphysical hfitTarget).not.mpr
      unfold endpoint at hsuffix
      omega
    have hframe := reverseBody_prefixFrame full command configuration capWords heapWords origin header base (childBase header q)
      counts parents node parent tested hb hq hw htestrep hs hf hheader hheaderAlloc
      (by rw [ht.2.2]; exact hwidth) (by rw [ht.2.2]; exact hmask) h1 hn hparent hptr hscalar ht.2.1
      (by rw [ht.2.2]; exact hnode) (by rw [ht.2.2]; exact hbase) (by rw [ht.2.2]; exact hcandidates)
      (by rw [ht.2.2]; exact hcounts) (by rw [ht.2.2]; exact hparents) (by rw [ht.2.2]; exact hreadParent)
      _ hneH8 hneTarget
    have hbound : origin + 5 + (reverseBody origin).length ≤ containing.length := by
      have hh := em.bound; rw [reverseBody_length, reverseProgramAt_length] at *; omega
    rw [show clock = 5 + (clock - 5) by omega, run_add, fetched_reverse_test em rom state hp ha,
      PA17A19RuntimeRanks008.last_prefix rom containing (reverseBodyLead origin) (.jumpIfZero .flag .old) (origin + 5) hbound
        (reverse_body_code em) (reverseBodyLead_straight origin) em.words em.pcfit tested htestpc
        (by rw [executeOps_halted, ha]) (clock - 5) (by rw [reverseBodyLead_length]; omega)]
    exact (hframe (clock - 5) (by rw [reverseBody_length]; omega)).trans (congrFun ht.2.2 _)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
