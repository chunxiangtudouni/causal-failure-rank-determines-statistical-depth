module

public import PaperProofs.Structure.PSTR_ArbitraryCount_071
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeHeader_011g

/-! The actual original count producer feeds the actual82-op Header in the
SAME containing program. All arrays and header inputs are produced by the
run, not qualifications added to original controller callers. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeEntry020

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PSTRWordSegments

abbrev wordBits {q : Nat} (full : List (Finset (Fin q))) : Nat := indexWidth 32 full.length q
abbrev capacity {q : Nat} (full : List (Finset (Fin q))) : Nat :=
  capacityWords 8192 full.length q (treeSize q full)
abbrev workspace {q : Nat} (full : List (Finset (Fin q))) : Nat :=
  PSTRQueryLayout.physicalWorkspace full (capacity full) (wordBits full)
abbrev header {q : Nat} (full : List (Finset (Fin q))) : Nat :=
  PA17A19RuntimeHeader011.head full (capacity full) (wordBits full)

structure HeaderReady {q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (before after : WordState (wordBits full)) : Prop where
  active : after.halted = false
  pc : after.pc = BitVec.ofNat (wordBits full) (5 * 621)
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

theorem from_counts {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (whole : List PackingOp)
    (em : PA17A19RuntimeHeader011.Embedded (wordBits full) 539 whole)
    (state : WordState (wordBits full))
    (complete : PSTRCountComplete.Complete full configuration 61 (capacity full) state)
    (hstage : configuration.stage = stage.val) :
    HeaderReady full configuration stage hq state
      (packingRun (callInput q full command) whole 82 state) := by
  let rom := callInput q full command
  have hb := PA17A19QueryBridgeNumeric006b.bits_eight full.length q
  have bitmap : tableWords full.length q (treeSize q full) + q ≤ capacity full := by
    simp only [capacity, capacityWords, ne_of_gt hq, ite_false]
    omega
  have hscalar := PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)
  rcases PA17A19RuntimeHeader011.original_numeric_room full stage 8192 8192 hq hl
    (by decide) (by decide) (by decide) with ⟨hN, hqr, htr, hrr, hrow, _, hhead⟩
  have hp : state.pc = BitVec.ofNat (wordBits full) (5 * 539) := by
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
  have views := PSTRCountComplete.logical_views full configuration 61 hq state complete
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
  refine ⟨result.1, result.2.1, result.2.2.1, hrep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame, ?_⟩
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

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeEntry020
