module

public import Structure.PA17_A19QueryBridge_RuntimeRelocate_029a
public import Structure.PA17_A19QueryBridge_RuntimeQuery_026c

/-! Relocate only the existing Header82+query-tail719 segment.
The generic original CountComplete enters at origin+478 and the actual
same-run segment exits ACTIVE at origin+1279. No raw producer, return
jump, shared exit, q0, dispatcher or intermediate HALT is invented here. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRelocate029

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeEntry020

def suffixClock (q size : Nat) : Nat := 82 + PA17A19RuntimeQuery026.tailClock q size

structure QueryReady {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (origin : Nat) (whole : List PackingOp) (before after : WordState (wordBits full)) : Prop where
  header : HeaderReady full command configuration stage hq origin whole before
    (packingRun (callInput q full command) whole 82 before)
  tail : PA17A19RuntimeQuery026.TailComplete full command configuration stage hq
    (capacity full) (allocatedWords full) (origin + 560) whole
    (packingRun (callInput q full command) whole 82 before) after
  correct : ReplyCorrect q (callback q full stage configuration.used) (replyState q (capacity full) after)
  active : after.halted = false
  pc : after.pc = BitVec.ofNat (wordBits full) (5 * (origin + 1279))
  address : after.register .address = BitVec.ofNat (wordBits full) (PA17A19RuntimeEntry020.header full)
  safe : ∀ clock < suffixClock q (treeSize q full), PSTRCountKernel.AtSafe (callInput q full command) whole
    (allocatedWords full) (packingRun (callInput q full command) whole clock before)
  represents : ∀ clock ≤ suffixClock q (treeSize q full), HeapRepresents q full (capacity full) configuration
    (packingRun (callInput q full command) whole clock before).heap
  capacityBound : ∀ clock ≤ suffixClock q (treeSize q full), CapacityPrefixBounded q (capacity full)
    (logicalHeap q (capacity full) (packingRun (callInput q full command) whole clock before).heap)
  leading : ∀ clock ≤ suffixClock q (treeSize q full), ∀ physical < PA17A19RuntimeEntry020.header full,
    (packingRun (callInput q full command) whole clock before).heap (BitVec.ofNat (wordBits full) physical) =
      before.heap (BitVec.ofNat (wordBits full) physical)
  high : ∀ clock ≤ suffixClock q (treeSize q full), ∀ physical, Fits (wordBits full) physical →
    PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
      (packingRun (callInput q full command) whole clock before).heap (BitVec.ofNat (wordBits full) physical) =
        before.heap (BitVec.ofNat (wordBits full) physical)
  table : ∀ clock ≤ suffixClock q (treeSize q full), ∀ address < tableWords full.length q (treeSize q full),
    logicalHeap q (capacity full) (packingRun (callInput q full command) whole clock before).heap address =
      logicalHeap q (capacity full) before.heap address
  trace : (packingDynamicTrace (callInput q full command) whole (suffixClock q (treeSize q full)) before).length ≤
    12 * suffixClock q (treeSize q full)

theorem from_header {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (hl : LaminarSchedule full) (whole : List PackingOp)
    (emTests : PA17A19RuntimeTests010.Embedded (wordBits full) (origin + 560) whole)
    (emRanks : PA17A19RuntimeRanks008.Embedded (wordBits full) (origin + 915) whole)
    (emSelector : PA17A19RuntimeSelect009.CoreEmbedded (wordBits full) (origin + 966) whole)
    (emFooter : PA17A19RuntimeReply016.Embedded (wordBits full) (origin + 1247) whole)
    (initial : WordState (wordBits full))
    (headerPost : HeaderReady full command configuration stage hq origin whole initial
      (packingRun (callInput q full command) whole 82 initial)) :
    QueryReady full command configuration stage hq origin whole initial
      (packingRun (callInput q full command) whole (suffixClock q (treeSize q full)) initial) := by
  let rom := callInput q full command
  let before := packingRun rom whole 82 initial
  have ranks : PA17A19RuntimeRanks008.Embedded (wordBits full) ((origin + 560) + 355) whole := by
    simpa only [Nat.add_assoc] using emRanks
  have selector : PA17A19RuntimeSelect009.CoreEmbedded (wordBits full) ((origin + 560) + 406) whole := by
    simpa only [Nat.add_assoc] using emSelector
  have footer : PA17A19RuntimeReply016.Embedded (wordBits full) ((origin + 560) + 687) whole := by
    simpa only [Nat.add_assoc] using emFooter
  have tail := PA17A19RuntimeQuery026.actual_tail_complete_8192 full command configuration stage hq hl whole
    emTests ranks selector footer before headerPost.data.represents headerPost.data.width headerPost.data.mask
    headerPost.data.address headerPost.data.pc headerPost.data.active headerPost.data.inputs headerPost.data.activeWord
  have run : packingRun rom whole (suffixClock q (treeSize q full)) initial =
      packingRun rom whole (PA17A19RuntimeQuery026.tailClock q (treeSize q full)) before := by
    rw [suffixClock, PSTRWordSegments.run_add]
  have fields (clock : Nat) (hc : clock ≤ suffixClock q (treeSize q full)) :
      HeapRepresents q full (capacity full) configuration (packingRun rom whole clock initial).heap ∧
      (∀ physical < PA17A19RuntimeEntry020.header full,
        (packingRun rom whole clock initial).heap (BitVec.ofNat (wordBits full) physical) = initial.heap (BitVec.ofNat (wordBits full) physical)) ∧
      (∀ physical, Fits (wordBits full) physical → PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
        (packingRun rom whole clock initial).heap (BitVec.ofNat (wordBits full) physical) = initial.heap (BitVec.ofNat (wordBits full) physical)) ∧
      (∀ address < tableWords full.length q (treeSize q full),
        logicalHeap q (capacity full) (packingRun rom whole clock initial).heap address = logicalHeap q (capacity full) initial.heap address) := by
    by_cases he : clock ≤ 82
    · exact ⟨headerPost.represents clock he, headerPost.leading clock he, headerPost.high clock he, headerPost.table clock he⟩
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show 82 ≤ clock by omega)
      have hx : extra ≤ PA17A19RuntimeQuery026.tailClock q (treeSize q full) := by unfold suffixClock at hc; omega
      rw [PSTRWordSegments.run_add]
      refine ⟨tail.prefix_represents extra hx, ?_, ?_, ?_⟩
      · intro physical hp
        exact (tail.prefix_low extra hx physical (by change physical < PA17A19RuntimeEntry020.header full + 4; omega)).trans
          (headerPost.leading 82 le_rfl physical hp)
      · intro physical hfit hp
        exact (tail.prefix_high extra hx physical hfit hp).trans (headerPost.high 82 le_rfl physical hfit hp)
      · intro address ha
        exact (tail.prefix_table extra hx address ha).trans (headerPost.table 82 le_rfl address ha)
  refine ⟨headerPost, ?_, ?_, ?_, ?_, ?_, ?_, (fun clock hc => (fields clock hc).1), ?_,
    (fun clock hc => (fields clock hc).2.1), (fun clock hc => (fields clock hc).2.2.1),
    (fun clock hc => (fields clock hc).2.2.2), packingDynamicTrace_length_le rom whole _ initial⟩
  · rw [run]
    exact tail
  · rw [run]
    exact tail.correct
  · rw [run]
    exact tail.active
  · rw [run]
    simpa only [Nat.add_assoc] using tail.pc
  · rw [run]
    exact tail.header
  · intro clock hc
    by_cases he : clock < 82
    · exact headerPost.safe clock he
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show 82 ≤ clock by omega)
      have hx : extra < PA17A19RuntimeQuery026.tailClock q (treeSize q full) := by unfold suffixClock at hc; omega
      rw [PSTRWordSegments.run_add]
      rcases tail.prefix_safe extra hx with ⟨active, _, inCode, op, decoded, access⟩
      exact ⟨active, inCode, op, decoded, access⟩
  · intro clock hc
    exact PSTRArbitraryOutside.represents_capacity full configuration _ _ hq (fields clock hc).1

theorem from_counts_query {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (hq : 0 < q) (hl : LaminarSchedule full) (whole : List PackingOp)
    (emHeader : CodeAt (wordBits full) origin whole)
    (emTests : PA17A19RuntimeTests010.Embedded (wordBits full) (origin + 560) whole)
    (emRanks : PA17A19RuntimeRanks008.Embedded (wordBits full) (origin + 915) whole)
    (emSelector : PA17A19RuntimeSelect009.CoreEmbedded (wordBits full) (origin + 966) whole)
    (emFooter : PA17A19RuntimeReply016.Embedded (wordBits full) (origin + 1247) whole)
    (state : WordState (wordBits full))
    (complete : PSTRCountComplete.Complete full configuration origin (capacity full) state) :
    QueryReady full command configuration (cursor full configuration command allowed) hq origin whole state
      (packingRun (callInput q full command) whole (suffixClock q (treeSize q full)) state) := by
  exact from_header full command configuration _ hq hl whole emTests emRanks emSelector emFooter state
    (from_allowed_counts full command configuration allowed hq hl whole emHeader state complete)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRelocate029
