module

public import PaperProofs.Structure.PSTR_HD_HeadsIteration_077

/-! The complete actual nonterminal controller iteration with the ORIGINAL
callback/rank and ORIGINAL scanPrefix. All rank/bad data are internal register
facts from the actual query segment; no such values enter the original ROM. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem original_scan_iteration {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (stage : Fin full.length) (capWords origin : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords ⟨stage.val, used, false⟩ state.heap)
    (recorded : RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
      (scanPrefix q full used stage.val) state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 40))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits (endpoint full capWords bits))
    (hold : state.register .old = BitVec.ofNat bits stage.val)
    (hindex : state.register .index = BitVec.ofNat bits full.length)
    (hbad : state.register .fresh = BitVec.ofNat bits (encodeRank q (badAt q full used stage)))
    (hN : Fits bits full.length) (hqfit : Fits bits (q + 3))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 10 + full.length)) :
    ∃ steps ≤ 40,
    let after := packingRun (callInput q full .query) whole steps state
    after.pc = BitVec.ofNat bits 0 ∧ after.halted = false ∧
    HeapRepresents q full capWords ⟨stage.val + 1, used, false⟩ after.heap ∧
    RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
      (scanPrefix q full used (stage.val + 1)) after.heap := by
  let R := encodeRank q (PSTRHeadScan.initialRank q full used)
  let B := encodeRank q (badAt q full used stage)
  let entries := scanPrefix q full used stage.val
  let E := endpoint full capWords bits
  have hlen : entries.length ≤ stage.val := scanPrefix_length_le q full used stage.val
  have heEntry : Fits bits (E + 10 + entries.length + 1) :=
    (show E + 10 + entries.length + 1 ≤ E + 10 + full.length by have h := stage.isLt; omega).trans_lt he
  have hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset) := by
    intro offset hoffset
    have hmeta := endpoint_metadata_after full capWords hq (bits := bits)
    exact (show 4 + packedCapacityWords q capWords bits + offset < E + 10 + full.length by omega).trans_le he.le
  have hB : Fits bits (B + 1) :=
    (show B + 1 ≤ q + 3 by have h := bad_encoded_bound q full hl used stage; omega).trans_lt hqfit
  have hR := initial_encoded_bound q full hl used
  have hq2 : Fits bits (q + 2) := (show q + 2 ≤ q + 3 by omega).trans_lt hqfit
  have hgate : headAt q full used stage.val = headGate q R B := by
    rw [headAt, dite_eq_left stage.isLt]
  have hlist : (if headGate q R B then entries ++ [stage.val] else entries) =
      scanPrefix q full used (stage.val + 1) := by
    rw [scanPrefix_succ, hgate]
    by_cases hg : headGate q R B = true <;> simp [hg, entries]
  obtain ⟨steps, hsteps, result⟩ := scan_iteration full ⟨stage.val, used, false⟩ capWords origin R B entries whole
    hbound hcode hwords hpcfit state hb hq rep recorded hp ha haddr hold hindex hbad stage.isLt hN hR hq2 hB bitmap hr hi heEntry
  refine ⟨steps, hsteps, ?_⟩
  dsimp only at result ⊢
  simpa only [hlist, nextConfiguration] using result

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
