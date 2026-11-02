module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeEntry_020d
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeQuery_026c

/-! One original raw arbitrary-register query call: counts, Header, Tests,
Ranks, canonical selector and callback footer execute in the SAME program.
All prefix properties below refer to that one actual run. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeEntry020

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def queryClock (countSteps q size : Nat) : Nat :=
  countSteps + 82 + PA17A19RuntimeQuery026.tailClock q size

structure RawQueryPost {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (whole : List PackingOp) (initial : WordState (wordBits full)) (countSteps : Nat) : Prop where
  entry : RawHeaderPost full command configuration stage hq whole initial countSteps
  tail : PA17A19RuntimeQuery026.TailComplete full command configuration stage hq
    (capacity full) (allocatedWords full) 621 whole
    (packingRun (callInput q full command) whole (countSteps + 82) initial)
    (packingRun (callInput q full command) whole (queryClock countSteps q (treeSize q full)) initial)
  correct : ReplyCorrect q (callback q full stage configuration.used)
    (replyState q (capacity full)
      (packingRun (callInput q full command) whole (queryClock countSteps q (treeSize q full)) initial))
  active : (packingRun (callInput q full command) whole (queryClock countSteps q (treeSize q full)) initial).halted = false
  pc : (packingRun (callInput q full command) whole (queryClock countSteps q (treeSize q full)) initial).pc =
    BitVec.ofNat (wordBits full) (5 * 1340)
  address : (packingRun (callInput q full command) whole (queryClock countSteps q (treeSize q full)) initial).register .address =
    BitVec.ofNat (wordBits full) (header full)
  safe : ∀ clock < queryClock countSteps q (treeSize q full),
    PSTRCountKernel.AtSafe (callInput q full command) whole (allocatedWords full)
      (packingRun (callInput q full command) whole clock initial)
  represents : ∀ clock ≤ queryClock countSteps q (treeSize q full), HeapRepresents q full (capacity full) configuration
    (packingRun (callInput q full command) whole clock initial).heap
  capacityBound : ∀ clock ≤ queryClock countSteps q (treeSize q full), CapacityPrefixBounded q (capacity full)
    (logicalHeap q (capacity full) (packingRun (callInput q full command) whole clock initial).heap)
  low : ∀ clock ≤ queryClock countSteps q (treeSize q full), ∀ physical, Fits (wordBits full) physical → physical < workspace full →
    (packingRun (callInput q full command) whole clock initial).heap (BitVec.ofNat (wordBits full) physical) =
      initial.heap (BitVec.ofNat (wordBits full) physical)
  high : ∀ clock ≤ queryClock countSteps q (treeSize q full), ∀ physical, Fits (wordBits full) physical →
    PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
    (packingRun (callInput q full command) whole clock initial).heap (BitVec.ofNat (wordBits full) physical) =
      initial.heap (BitVec.ofNat (wordBits full) physical)
  table : ∀ clock ≤ queryClock countSteps q (treeSize q full), ∀ address < tableWords full.length q (treeSize q full),
    logicalHeap q (capacity full) (packingRun (callInput q full command) whole clock initial).heap address =
      logicalHeap q (capacity full) initial.heap address
  trace : (packingDynamicTrace (callInput q full command) whole
      (queryClock countSteps q (treeSize q full)) initial).length ≤
    12 * (8 * CapacityBits.width q + 148 + 501 * treeSize q full + PA17A19RuntimeQuery026.tailClock q (treeSize q full))

theorem query_of_header {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (hl : LaminarSchedule full) (whole : List PackingOp)
    (emTests : PA17A19RuntimeTests010.Embedded (wordBits full) 621 whole)
    (emRanks : PA17A19RuntimeRanks008.Embedded (wordBits full) 976 whole)
    (emSelector : PA17A19RuntimeSelect009.CoreEmbedded (wordBits full) 1027 whole)
    (emFooter : PA17A19RuntimeReply016.Embedded (wordBits full) 1308 whole)
    (initial : WordState (wordBits full)) (countSteps : Nat)
    (entry : RawHeaderPost full command configuration stage hq whole initial countSteps)
    (safe : ∀ clock < countSteps + 82, PSTRCountKernel.AtSafe (callInput q full command) whole
      (allocatedWords full) (packingRun (callInput q full command) whole clock initial)) :
    RawQueryPost full command configuration stage hq whole initial countSteps := by
  let rom := callInput q full command
  let before := packingRun rom whole (countSteps + 82) initial
  have tail := PA17A19RuntimeQuery026.actual_tail_complete_8192 full command configuration stage hq hl whole
    emTests emRanks emSelector emFooter before entry.header.represents entry.header.width entry.header.mask
    entry.header.address entry.header.pc entry.header.active entry.header.inputs entry.header.activeWord
  have run : packingRun rom whole (queryClock countSteps q (treeSize q full)) initial =
      packingRun rom whole (PA17A19RuntimeQuery026.tailClock q (treeSize q full)) before := by
    rw [queryClock, PSTRWordSegments.run_add]
  have fields (clock : Nat) (hc : clock ≤ queryClock countSteps q (treeSize q full)) :
      HeapRepresents q full (capacity full) configuration (packingRun rom whole clock initial).heap ∧
      (∀ physical, Fits (wordBits full) physical → physical < workspace full →
        (packingRun rom whole clock initial).heap (BitVec.ofNat (wordBits full) physical) = initial.heap (BitVec.ofNat (wordBits full) physical)) ∧
      (∀ physical, Fits (wordBits full) physical → PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
        (packingRun rom whole clock initial).heap (BitVec.ofNat (wordBits full) physical) = initial.heap (BitVec.ofNat (wordBits full) physical)) ∧
      (∀ address < tableWords full.length q (treeSize q full),
        logicalHeap q (capacity full) (packingRun rom whole clock initial).heap address = logicalHeap q (capacity full) initial.heap address) := by
    by_cases he : clock ≤ countSteps + 82
    · exact ⟨entry.represents clock he, entry.low clock he, entry.high clock he, entry.table clock he⟩
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show countSteps + 82 ≤ clock by omega)
      have hx : extra ≤ PA17A19RuntimeQuery026.tailClock q (treeSize q full) := by
        unfold queryClock at hc
        omega
      rw [PSTRWordSegments.run_add]
      refine ⟨tail.prefix_represents extra hx, ?_, ?_, ?_⟩
      · intro physical hfit hp
        apply (tail.prefix_low extra hx physical ?_).trans (entry.low (countSteps + 82) le_rfl physical hfit hp)
        change physical < PSTRQueryLayout.header (workspace full) (treeSize q full) + 4
        unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
        omega
      · intro physical hfit hp
        exact (tail.prefix_high extra hx physical hfit hp).trans (entry.high (countSteps + 82) le_rfl physical hfit hp)
      · intro address ha
        exact (tail.prefix_table extra hx address ha).trans (entry.table (countSteps + 82) le_rfl address ha)
  refine ⟨entry, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run]
    exact tail
  · rw [run]
    exact tail.correct
  · rw [run]
    exact tail.active
  · rw [run]
    exact tail.pc
  · rw [run]
    exact tail.header
  · intro clock hc
    by_cases he : clock < countSteps + 82
    · exact safe clock he
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show countSteps + 82 ≤ clock by omega)
      have hx : extra < PA17A19RuntimeQuery026.tailClock q (treeSize q full) := by
        unfold queryClock at hc
        omega
      rw [PSTRWordSegments.run_add]
      rcases tail.prefix_safe extra hx with ⟨active, _, inCode, op, decoded, access⟩
      exact ⟨active, inCode, op, decoded, access⟩
  · exact fun clock hc => (fields clock hc).1
  · intro clock hc
    exact PSTRArbitraryOutside.represents_capacity full configuration _ _ hq (fields clock hc).1
  · exact fun clock hc => (fields clock hc).2.1
  · exact fun clock hc => (fields clock hc).2.2.1
  · exact fun clock hc => (fields clock hc).2.2.2
  · have ht := packingDynamicTrace_length_le rom whole (queryClock countSteps q (treeSize q full)) initial
    have hu := entry.upper
    have hu' : countSteps + 82 ≤ 8 * CapacityBits.width q + 148 + 501 * treeSize q full := by
      simp only [treeSize, ne_of_gt hq, ite_false]
      omega
    apply ht.trans
    apply Nat.mul_le_mul_left
    unfold queryClock
    omega

theorem actual_raw_query {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (whole : List PackingOp) (cb : PSTRBootstrapSlices.Contains whole)
    (co : PSTROuterCountCode.Contains whole 61)
    (emHeader : PA17A19RuntimeHeader011.Embedded (wordBits full) 539 whole)
    (emTests : PA17A19RuntimeTests010.Embedded (wordBits full) 621 whole)
    (emRanks : PA17A19RuntimeRanks008.Embedded (wordBits full) 976 whole)
    (emSelector : PA17A19RuntimeSelect009.CoreEmbedded (wordBits full) 1027 whole)
    (emFooter : PA17A19RuntimeReply016.Embedded (wordBits full) 1308 whole)
    (hq : 0 < q) (hl : LaminarSchedule full) (initial : WordState (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration initial.heap)
    (hp : initial.pc = BitVec.ofNat (wordBits full) 0) (ha : initial.halted = false) :
    ∃ countSteps, RawQueryPost full command configuration (cursor full configuration command allowed) hq whole initial countSteps := by
  obtain ⟨countSteps, headerPost, safe⟩ := actual_raw_header_safe full command configuration allowed whole cb co emHeader hq hl initial rep hp ha
  exact ⟨countSteps, query_of_header full command configuration _ hq hl whole emTests emRanks emSelector emFooter initial countSteps headerPost safe⟩

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeEntry020
