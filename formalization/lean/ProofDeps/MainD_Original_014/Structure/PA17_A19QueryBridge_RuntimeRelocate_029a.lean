module

public import Structure.PA17_A19QueryBridge_RuntimeEntry_020d

/-! Necessary code relocation only. A genuinely generic Complete(origin)
feeds the existing generic Header at origin+478 and exits at origin+560.
All physical layout, data and numeric obligations stay the original ones. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRelocate029

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeEntry020

abbrev CodeAt (bits origin : Nat) (whole : List PackingOp) :=
  PA17A19RuntimeHeader011.Embedded bits (origin + 478) whole

structure HeaderData {q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (origin : Nat) (before after : WordState (wordBits full)) : Prop where
  active : after.halted = false
  pc : after.pc = BitVec.ofNat (wordBits full) (5 * (origin + 560))
  address : after.register .address = BitVec.ofNat (wordBits full) (header full)
  represents : HeapRepresents q full (capacity full) configuration after.heap
  width : after.heap (BitVec.ofNat (wordBits full) (workspace full + 12)) =
    BitVec.ofNat (wordBits full) (CapacityBits.width q)
  mask : after.heap (BitVec.ofNat (wordBits full) (workspace full + 13)) =
    lowMask (wordBits full) (CapacityBits.width q)
  row : after.heap (BitVec.ofNat (wordBits full) (header full)) =
    BitVec.ofNat (wordBits full) (PA17A19RuntimeHeader011.row full stage)
  node : after.heap (BitVec.ofNat (wordBits full) (header full + 1)) =
    BitVec.ofNat (wordBits full) (PA17A19RuntimeHeader011.nodeWord full hq stage)
  activeWord : after.heap (BitVec.ofNat (wordBits full) (header full + 2)) =
    BitVec.ofNat (wordBits full) (PA17QueryHeader009.active full.length stage.val)
  stageWord : after.heap (BitVec.ofNat (wordBits full) (header full + 3)) =
    BitVec.ofNat (wordBits full) stage.val
  inputs : PA17QueryTests009.Inputs (prepareNormalization q full).indexed
    (PA17A19RuntimeHeader011.logicalHead full (capacity full))
    (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full (capacity full)))
    (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full (capacity full)) (treeSize q full))
    (PA17A19RuntimeHeader011.logicalHead full (capacity full) + 1)
    (PA17A19RuntimeHeader011.row full stage)
    (IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used)
    (IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage))
    (PA17QueryBudget015.node full hq stage) (logicalHeap q (capacity full) after.heap)
  leading : ∀ physical < header full,
    after.heap (BitVec.ofNat (wordBits full) physical) = before.heap (BitVec.ofNat (wordBits full) physical)
  high : ∀ physical, Fits (wordBits full) physical →
    PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
    after.heap (BitVec.ofNat (wordBits full) physical) = before.heap (BitVec.ofNat (wordBits full) physical)

theorem from_counts_data {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (whole : List PackingOp)
    (em : CodeAt (wordBits full) origin whole)
    (state : WordState (wordBits full))
    (complete : PSTRCountComplete.Complete full configuration origin (capacity full) state)
    (hstage : configuration.stage = stage.val) :
    HeaderData full configuration stage hq origin state
      (packingRun (callInput q full command) whole 82 state) := by
  let rom := callInput q full command
  have hb := PA17A19QueryBridgeNumeric006b.bits_eight full.length q
  have bitmap : tableWords full.length q (treeSize q full) + q ≤ capacity full := by
    simp only [capacity, capacityWords, ne_of_gt hq, ite_false]
    omega
  have hscalar := PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)
  rcases PA17A19RuntimeHeader011.original_numeric_room full stage 8192 8192 hq hl
    (by decide) (by decide) (by decide) with ⟨hN, hqr, htr, hrr, hrow, _, hhead⟩
  have hp : state.pc = BitVec.ofNat (wordBits full) (5 * (origin + 478)) := by
    simpa using complete.pc
  have result := PA17A19RuntimeHeader011.actual_header em full command configuration (capacity full)
    state stage hb hq complete.rep hstage hN hqr htr hrr hhead hp complete.active
  have run : packingRun rom whole 82 state = executeOps rom PA17A19RuntimeHeader011.program state := by
    rw [PA17A19RuntimeHeader011.actual_prefix em rom state hp complete.active 82
      (by rw [PA17A19RuntimeHeader011.program_length])]
    rw [List.take_of_length_le (by rw [PA17A19RuntimeHeader011.program_length])]
  have frame (physical : Nat) (hphysical : physical < header full) :
      (packingRun rom whole 82 state).heap (BitVec.ofNat (wordBits full) physical) =
        state.heap (BitVec.ofNat (wordBits full) physical) := by
    rw [run]
    simpa only [List.take_of_length_le (by rw [PA17A19RuntimeHeader011.program_length])] using
      PA17A19RuntimeHeader011.prefix_frame full command configuration (capacity full) state hb hq
        complete.rep hhead physical 82 hphysical
  have hrep : HeapRepresents q full (capacity full) configuration
      (packingRun rom whole 82 state).heap := by
    rw [run]
    simpa only [List.take_of_length_le (by rw [PA17A19RuntimeHeader011.program_length])] using
      PA17A19RuntimeHeader011.heap_represents full command configuration (capacity full) state hb hq
        complete.rep bitmap hscalar hhead 82
  have views := PSTRCountComplete.logical_views full configuration origin hq state complete
  have parentView : PA17HeapAncestors001.ParentHeapFor (prepareNormalization q full).indexed
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full (capacity full)) (treeSize q full))
      (logicalHeap q (capacity full) state.heap) := by
    simpa only [capacity, treeSize, ne_of_gt hq, ite_false] using views.2
  have inputs := PA17A19RuntimeHeader011.internal_inputs full command configuration (capacity full) state
    stage hb hq complete.rep hstage bitmap hscalar hN hqr htr hrr hrow hhead views.1 parentView
  have saved := PA17A19RuntimeHeader011.storedHeap_values state.heap (header full)
    (BitVec.ofNat (wordBits full) (PA17A19RuntimeHeader011.row full stage))
    (BitVec.ofNat (wordBits full) (PA17A19RuntimeHeader011.nodeWord full hq stage))
    (BitVec.ofNat (wordBits full) (PA17QueryHeader009.active full.length stage.val))
    (BitVec.ofNat (wordBits full) stage.val) hhead
  have hbase : PSTRCountWorkspace.base q full (capacity full) (wordBits full) = workspace full :=
    PSTRCountWorkspace.base_metadata_end q full hq (capacity full) (wordBits full)
  have width : state.heap (BitVec.ofNat (wordBits full) (workspace full + 12)) =
      BitVec.ofNat (wordBits full) (CapacityBits.width q) := by
    have h := complete.slots 0 (by decide)
    rw [hbase] at h
    simpa only [Nat.add_zero, ite_true] using h
  have mask : state.heap (BitVec.ofNat (wordBits full) (workspace full + 13)) =
      lowMask (wordBits full) (CapacityBits.width q) := by
    have h := complete.slots 1 (by decide)
    rw [hbase] at h
    have ha : workspace full + 12 + 1 = workspace full + 13 := by omega
    simpa only [Nat.one_ne_zero, ite_false, ite_true, ha] using h
  refine ⟨result.1, by simpa only [Nat.add_assoc] using result.2.1, result.2.2.1, hrep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame, ?_⟩
  · rw [frame _ (by
      unfold header workspace PA17A19RuntimeHeader011.head PSTRQueryLayout.header PSTRQueryLayout.parentsBase
        PSTRQueryLayout.countsBase
      omega)]
    exact width
  · rw [frame _ (by
      unfold header workspace PA17A19RuntimeHeader011.head PSTRQueryLayout.header PSTRQueryLayout.parentsBase
        PSTRQueryLayout.countsBase
      omega)]
    exact mask
  · rw [result.2.2.2]
    exact saved.1
  · rw [result.2.2.2]
    exact saved.2.1
  · rw [result.2.2.2]
    exact saved.2.2.1
  · rw [result.2.2.2]
    exact saved.2.2.2
  · rw [run]
    exact inputs
  · intro physical hphysical habove
    exact PA17A19RuntimeHeader011.actual_endpoint_frame em full command configuration (capacity full) state
      hb hq complete.rep hhead hp complete.active 82 le_rfl physical hphysical habove


theorem prefix_fields {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (whole : List PackingOp)
    (em : CodeAt (wordBits full) origin whole) (state : WordState (wordBits full))
    (complete : PSTRCountComplete.Complete full configuration origin (capacity full) state)
    (clock : Nat) (hc : clock ≤ 82) :
    let after := packingRun (callInput q full command) whole clock state
    HeapRepresents q full (capacity full) configuration after.heap ∧
    (∀ physical < header full,
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
  have run := PA17A19RuntimeHeader011.actual_prefix em (callInput q full command) state complete.pc complete.active clock
    (by simpa only [PA17A19RuntimeHeader011.program_length] using hc)
  dsimp only
  rw [run]
  refine ⟨PA17A19RuntimeHeader011.heap_represents full command configuration (capacity full) state hb hq
    complete.rep bitmap hscalar room.2.2.2.2.2.2 clock,
    (fun physical hphysical => PA17A19RuntimeHeader011.prefix_frame full command configuration (capacity full) state hb hq
      complete.rep room.2.2.2.2.2.2 physical clock hphysical), ?_, ?_⟩
  · intro physical hphysical habove
    exact PA17A19RuntimeHeader011.endpoint_frame full command configuration (capacity full) state hb hq
      complete.rep room.2.2.2.2.2.2 physical clock hphysical habove
  · intro address haddress
    apply PA17A19RuntimeHeader011.logical_prefix_frame full command configuration (capacity full) state hb hq
      complete.rep hscalar room.2.2.2.2.2.2 address clock
    unfold PA17A19RuntimeHeader011.logicalHead PSTRQueryLayout.header PSTRQueryLayout.parentsBase
      PSTRQueryLayout.countsBase PSTRQueryLayout.logicalWorkspace
    omega

structure HeaderReady {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (origin : Nat) (whole : List PackingOp) (before after : WordState (wordBits full)) : Prop where
  data : HeaderData full configuration stage hq origin before after
  represents : ∀ clock ≤ 82, HeapRepresents q full (capacity full) configuration
    (packingRun (callInput q full command) whole clock before).heap
  capacityBound : ∀ clock ≤ 82, CapacityPrefixBounded q (capacity full)
    (logicalHeap q (capacity full) (packingRun (callInput q full command) whole clock before).heap)
  leading : ∀ clock ≤ 82, ∀ physical < header full,
    (packingRun (callInput q full command) whole clock before).heap (BitVec.ofNat (wordBits full) physical) =
      before.heap (BitVec.ofNat (wordBits full) physical)
  high : ∀ clock ≤ 82, ∀ physical, Fits (wordBits full) physical →
    PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
      (packingRun (callInput q full command) whole clock before).heap (BitVec.ofNat (wordBits full) physical) =
        before.heap (BitVec.ofNat (wordBits full) physical)
  table : ∀ clock ≤ 82, ∀ address < tableWords full.length q (treeSize q full),
    logicalHeap q (capacity full) (packingRun (callInput q full command) whole clock before).heap address =
      logicalHeap q (capacity full) before.heap address
  safe : ∀ clock < 82, PSTRCountKernel.AtSafe (callInput q full command) whole (allocatedWords full)
    (packingRun (callInput q full command) whole clock before)

theorem from_counts {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (whole : List PackingOp)
    (em : CodeAt (wordBits full) origin whole) (state : WordState (wordBits full))
    (complete : PSTRCountComplete.Complete full configuration origin (capacity full) state)
    (hstage : configuration.stage = stage.val) :
    HeaderReady full command configuration stage hq origin whole state
      (packingRun (callInput q full command) whole 82 state) := by
  have fields := prefix_fields full command configuration stage hq hl whole em state complete
  refine ⟨from_counts_data full command configuration stage hq hl whole em state complete hstage,
    (fun clock hc => (fields clock hc).1), ?_, (fun clock hc => (fields clock hc).2.1),
    (fun clock hc => (fields clock hc).2.2.1), (fun clock hc => (fields clock hc).2.2.2), ?_⟩
  · intro clock hc
    exact PSTRArbitraryOutside.represents_capacity full configuration _ _ hq (fields clock hc).1
  · intro clock hc
    have room := PA17A19RuntimeHeader011.original_numeric_room full stage 8192 8192 hq hl
      (by decide) (by decide) (by decide)
    have hs : configuration.stage ≤ full.length := by
      rw [hstage]
      exact Nat.le_of_lt_succ stage.isLt
    rcases PA17A19RuntimeHeader011.actual_prefix_decoded em full command configuration (capacity full)
      (allocatedWords full) state (PA17A19QueryBridgeNumeric006b.bits_eight full.length q) hq
      complete.rep hs room.2.2.2.2.2.1 complete.pc complete.active clock hc with
      ⟨active, _, inCode, op, decoded, access⟩
    exact ⟨active, inCode, op, decoded, access⟩

theorem from_allowed_counts {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (hq : 0 < q) (hl : LaminarSchedule full) (whole : List PackingOp)
    (em : CodeAt (wordBits full) origin whole) (state : WordState (wordBits full))
    (complete : PSTRCountComplete.Complete full configuration origin (capacity full) state) :
    HeaderReady full command configuration (cursor full configuration command allowed) hq origin whole state
      (packingRun (callInput q full command) whole 82 state) := by
  exact from_counts full command configuration _ hq hl whole em state complete rfl

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRelocate029
