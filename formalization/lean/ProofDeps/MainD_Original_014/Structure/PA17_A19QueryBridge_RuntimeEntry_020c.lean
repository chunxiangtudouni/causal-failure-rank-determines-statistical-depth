module

public import Structure.PA17_A19QueryBridge_RuntimeEntry_020b
public import Structure.PSTR_ArbitraryOutside_086

/-! Original persistent data at every raw count+Header clock. The exact
table-word frame includes VOID payloads; it is not inferred from HeapRep
uniqueness. Count fetch/access is deliberately not inferred here. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeEntry020

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem header_prefix_fields {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (whole : List PackingOp)
    (em : PA17A19RuntimeHeader011.Embedded (wordBits full) 539 whole)
    (state : WordState (wordBits full))
    (complete : PSTRCountComplete.Complete full configuration 61 (capacity full) state)
    (clock : Nat) (hc : clock ≤ 82) :
    let after := packingRun (callInput q full command) whole clock state
    HeapRepresents q full (capacity full) configuration after.heap ∧
    (∀ physical < workspace full,
      after.heap (BitVec.ofNat (wordBits full) physical) = state.heap (BitVec.ofNat (wordBits full) physical)) ∧
    (∀ physical, Fits (wordBits full) physical → PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
      after.heap (BitVec.ofNat (wordBits full) physical) = state.heap (BitVec.ofNat (wordBits full) physical)) ∧
    (∀ address < tableWords full.length q (treeSize q full),
      logicalHeap q (capacity full) after.heap address = logicalHeap q (capacity full) state.heap address) := by
  have hb := PA17A19QueryBridgeNumeric006b.bits_eight full.length q
  have bitmap : tableWords full.length q (treeSize q full) + q ≤ capacity full := by
    simp only [capacity, capacityWords, ne_of_gt hq, ite_false]
    omega
  have hscalar := PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)
  have room := PA17A19RuntimeHeader011.original_numeric_room full stage 8192 8192 hq hl
    (by decide) (by decide) (by decide)
  have hp : state.pc = BitVec.ofNat (wordBits full) (5 * 539) := by simpa using complete.pc
  have run := PA17A19RuntimeHeader011.actual_prefix em (callInput q full command) state hp complete.active clock
    (by simpa only [PA17A19RuntimeHeader011.program_length] using hc)
  dsimp only
  rw [run]
  refine ⟨PA17A19RuntimeHeader011.heap_represents full command configuration (capacity full) state hb hq
    complete.rep bitmap hscalar room.2.2.2.2.2.2 clock, ?_, ?_, ?_⟩
  · intro physical hphysical
    apply PA17A19RuntimeHeader011.prefix_frame full command configuration (capacity full) state hb hq
      complete.rep room.2.2.2.2.2.2 physical clock
    change physical < PSTRQueryLayout.header (workspace full) (treeSize q full)
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  · intro physical hphysical habove
    exact PA17A19RuntimeHeader011.endpoint_frame full command configuration (capacity full) state hb hq
      complete.rep room.2.2.2.2.2.2 physical clock hphysical habove
  · intro address haddress
    apply PA17A19RuntimeHeader011.logical_prefix_frame full command configuration (capacity full) state hb hq
      complete.rep hscalar room.2.2.2.2.2.2 address clock
    unfold PA17A19RuntimeHeader011.logicalHead PSTRQueryLayout.header PSTRQueryLayout.parentsBase
      PSTRQueryLayout.countsBase PSTRQueryLayout.logicalWorkspace
    omega

structure RawHeaderPost {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (whole : List PackingOp) (initial : WordState (wordBits full)) (countSteps : Nat) : Prop where
  lower : 66 ≤ countSteps
  upper : countSteps ≤ 8 * CapacityBits.width q + 66 + 501 * (prepareNormalization q full).indexed.nodes.size
  counts : PSTRCountComplete.Complete full configuration 61 (capacity full)
    (packingRun (callInput q full command) whole countSteps initial)
  header : HeaderReady full configuration stage hq
    (packingRun (callInput q full command) whole countSteps initial)
    (packingRun (callInput q full command) whole (countSteps + 82) initial)
  represents : ∀ clock ≤ countSteps + 82, HeapRepresents q full (capacity full) configuration
    (packingRun (callInput q full command) whole clock initial).heap
  capacityBound : ∀ clock ≤ countSteps + 82, CapacityPrefixBounded q (capacity full)
    (logicalHeap q (capacity full) (packingRun (callInput q full command) whole clock initial).heap)
  low : ∀ clock ≤ countSteps + 82, ∀ physical, Fits (wordBits full) physical → physical < workspace full →
    (packingRun (callInput q full command) whole clock initial).heap (BitVec.ofNat (wordBits full) physical) =
      initial.heap (BitVec.ofNat (wordBits full) physical)
  high : ∀ clock ≤ countSteps + 82, ∀ physical, Fits (wordBits full) physical →
    PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
    (packingRun (callInput q full command) whole clock initial).heap (BitVec.ofNat (wordBits full) physical) =
      initial.heap (BitVec.ofNat (wordBits full) physical)
  table : ∀ clock ≤ countSteps + 82, ∀ address < tableWords full.length q (treeSize q full),
    logicalHeap q (capacity full) (packingRun (callInput q full command) whole clock initial).heap address =
      logicalHeap q (capacity full) initial.heap address

theorem actual_raw_header_post {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (whole : List PackingOp) (cb : PSTRBootstrapSlices.Contains whole)
    (co : PSTROuterCountCode.Contains whole 61)
    (em : PA17A19RuntimeHeader011.Embedded (wordBits full) 539 whole)
    (hq : 0 < q) (hl : LaminarSchedule full) (initial : WordState (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration initial.heap)
    (hp : initial.pc = BitVec.ofNat (wordBits full) 0) (ha : initial.halted = false) :
    ∃ countSteps, RawHeaderPost full command configuration (cursor full configuration command allowed) hq
      whole initial countSteps := by
  let rom := callInput q full command
  let stage := cursor full configuration command allowed
  obtain ⟨steps, lower, upper, complete, frames, _, table⟩ := PSTRArbitraryOutside.actual_complete full command
    configuration whole cb co em.words em.pcfit hq hl initial rep hp ha
  let counted := packingRun rom whole steps initial
  have hh := from_counts full command configuration stage hq hl whole em counted complete rfl
  have hbase : PSTRCountWorkspace.base q full (capacity full) (wordBits full) = workspace full :=
    PSTRCountWorkspace.base_metadata_end q full hq (capacity full) (wordBits full)
  have lowhigh (clock : Nat) (hc : clock ≤ steps) (physical : Nat) (hfit : Fits (wordBits full) physical)
      (hposition : physical < workspace full ∨ PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical) :
      (packingRun rom whole clock initial).heap (BitVec.ofNat (wordBits full) physical) =
        initial.heap (BitVec.ofNat (wordBits full) physical) := by
    apply (frames clock hc).2 physical hfit
    rw [hbase]
    simpa only [treeSize, ne_of_gt hq, ite_false] using hposition
  have prefixRep (clock : Nat) (hc : clock ≤ steps + 82) :
      HeapRepresents q full (capacity full) configuration (packingRun rom whole clock initial).heap := by
    by_cases he : clock ≤ steps
    · exact (frames clock he).1
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show steps ≤ clock by omega)
      rw [PSTRWordSegments.run_add]
      exact (header_prefix_fields full command configuration stage hq hl whole em counted complete extra (by omega)).1
  refine ⟨steps, lower, upper, complete, ?_, prefixRep, ?_, ?_, ?_, ?_⟩
  · rw [PSTRWordSegments.run_add]
    exact hh
  · intro clock hc
    exact PSTRArbitraryOutside.represents_capacity full configuration _ _ hq (prefixRep clock hc)
  · intro clock hc physical hfit hphysical
    by_cases he : clock ≤ steps
    · exact lowhigh clock he physical hfit (Or.inl hphysical)
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show steps ≤ clock by omega)
      rw [PSTRWordSegments.run_add]
      exact ((header_prefix_fields full command configuration stage hq hl whole em counted complete extra
        (by omega)).2.1 physical hphysical).trans (lowhigh steps le_rfl physical hfit (Or.inl hphysical))
  · intro clock hc physical hfit hphysical
    by_cases he : clock ≤ steps
    · exact lowhigh clock he physical hfit (Or.inr hphysical)
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show steps ≤ clock by omega)
      rw [PSTRWordSegments.run_add]
      exact ((header_prefix_fields full command configuration stage hq hl whole em counted complete extra
        (by omega)).2.2.1 physical hfit hphysical).trans (lowhigh steps le_rfl physical hfit (Or.inr hphysical))
  · intro clock hc address haddress
    by_cases he : clock ≤ steps
    · exact table clock he address haddress
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show steps ≤ clock by omega)
      rw [PSTRWordSegments.run_add]
      exact ((header_prefix_fields full command configuration stage hq hl whole em counted complete extra
        (by omega)).2.2.2 address haddress).trans (table steps le_rfl address haddress)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeEntry020
