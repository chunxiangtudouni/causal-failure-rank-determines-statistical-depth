module

public import PaperProofs.Structure.PSTR_HD_HeadsRecorded_060
public import PaperProofs.Structure.PSTR_HD_HeadsBackJump_061

/-! Exact ORIGINAL headWords serialization from the actual recorded heap and
actual7op terminal write. The recorded heap must come from the actual same-run
producer/scan; this theorem does not assume a query oracle or replace that run. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM RawTreePreprocessingClaims
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem heapWordsAt_eq {bits : Nat} (heap : BitVec bits → BitVec bits) (base : Nat) (words : List Nat)
    (hf : ∀ position < words.length, Fits bits (words.getD position 0))
    (hw : ∀ position < words.length, heap (BitVec.ofNat bits (base + position)) = BitVec.ofNat bits (words.getD position 0)) :
    heapWordsAt heap base words.length = words := by
  apply List.ext_getElem
  · simp only [heapWordsAt, List.length_map, List.length_range]
  · intro position _ hright
    simp only [heapWordsAt, List.getElem_map, List.getElem_range]
    rw [hw position hright, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hf position hright),
      List.getD_eq_getElem words 0 hright]

theorem finish_recorded_word {bits : Nat} (rom : PhysicalROM) (endpoint q rank : Nat) (entries : List Nat)
    (state : WordState bits) (recorded : RecordedHeads endpoint q rank entries state.heap)
    (hp : state.register .address = BitVec.ofNat bits endpoint) (he : Fits bits (endpoint + 10 + entries.length))
    (position : Nat) (hposition : position < ([rank, entries.length] ++ entries).length) :
    (executeOps rom headsFinish state).heap (BitVec.ofNat bits (outputBase endpoint + position)) =
      BitVec.ofNat bits (([rank, entries.length] ++ entries).getD position 0) := by
  by_cases hzero : position = 0
  · subst position
    simpa only [outputBase, Nat.add_zero, List.cons_append, List.nil_append, List.getD_cons_zero] using
      finish_recorded_rank rom endpoint q rank entries state recorded hp
        ((show endpoint + 9 ≤ endpoint + 10 + entries.length by omega).trans_lt he)
  · by_cases hone : position = 1
    · subst position
      simpa only [outputBase, Nat.add_assoc, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] using
        finish_recorded_count rom endpoint q rank entries state recorded hp
    · have hpos : position - 2 < entries.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hposition
        omega
      have haddr : outputBase endpoint + position = endpoint + 10 + (position - 2) := by unfold outputBase; omega
      have hget : ([rank, entries.length] ++ entries).getD position 0 = entries.getD (position - 2) 0 :=
        List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      rw [haddr, hget]
      exact finish_recorded_entries rom endpoint q rank entries state recorded hp he _ hpos

theorem finish_serialized {bits : Nat} (rom : PhysicalROM) (endpoint q rank : Nat) (entries : List Nat)
    (state : WordState bits) (recorded : RecordedHeads endpoint q rank entries state.heap)
    (hp : state.register .address = BitVec.ofNat bits endpoint) (he : Fits bits (endpoint + 10 + entries.length))
    (hr : Fits bits rank) (hk : Fits bits entries.length)
    (hf : ∀ position < entries.length, Fits bits (entries.getD position 0)) :
    heapWordsAt (executeOps rom headsFinish state).heap (outputBase endpoint) (2 + entries.length) =
      [rank, entries.length] ++ entries := by
  have hw := finish_recorded_word rom endpoint q rank entries state recorded hp he
  have hfit (position : Nat) (hposition : position < ([rank, entries.length] ++ entries).length) :
      Fits bits (([rank, entries.length] ++ entries).getD position 0) := by
    by_cases hzero : position = 0
    · subst position
      simpa using hr
    · by_cases hone : position = 1
      · subst position
        simpa using hk
      · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
        apply hf
        simp only [List.length_cons, List.length_nil]
        simp only [List.length_append, List.length_cons, List.length_nil] at hposition
        omega
  simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using
    heapWordsAt_eq _ (outputBase endpoint) ([rank, entries.length] ++ entries) hfit hw

theorem finish_original_headWords {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (endpoint : Nat) (state : WordState bits)
    (recorded : RecordedHeads endpoint q (encodeRank q (PSTRHeadScan.initialRank q full used))
      (scanPrefix q full used full.length) state.heap)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (he : Fits bits (endpoint + 10 + (scanPrefix q full used full.length).length))
    (hr : Fits bits (encodeRank q (PSTRHeadScan.initialRank q full used)))
    (hk : Fits bits (scanPrefix q full used full.length).length)
    (hf : ∀ position < (scanPrefix q full used full.length).length,
      Fits bits ((scanPrefix q full used full.length).getD position 0)) :
    heapWordsAt (executeOps (callInput q full .query) headsFinish state).heap (outputBase endpoint)
      (headWords q full used).length = headWords q full used := by
  rw [headWords_scan q full hl used]
  simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using
    finish_serialized (callInput q full .query) endpoint q _ _ state recorded hp he hr hk hf

theorem original_output_room8192 {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (capWords : Nat) (hq : 0 < q) (hl : LaminarSchedule full) :
    outputBase (endpoint full capWords bits) + (headWords q full used).length ≤
      physicalHeaderWords + packedCapacityWords q capWords bits + 8192 * (full.length + q + treeSize q full + 1) := by
  have hroom := heads_room8192 full capWords hq hl (bits := bits)
  have hcount := scanPrefix_length_le q full used full.length
  rw [headWords_scan q full hl used]
  simp only [List.length_append, List.length_cons, List.length_nil]
  unfold outputBase
  omega

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
