module

public import Structure.PA06_A19Prepare_CompactParents035Loop
public import Structure.PA06_A19Prepare_CompactOrdering034Entry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! The original raw program, from natInitial through checker, gate, compact
initialization, retention, sorting and the full361-op parent search. The
prepared-parent semantics and inverse source bounds are derived from the
actual sorting output. Every strict clock belongs to this one run. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Entry

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

abbrev parentStart := PA06A19PrepareCompactCandidates007.parentStart
abbrev inputStart := PA06A19PrepareCompactCandidates007.inputStart
abbrev orderingStart := PA06A19PrepareCompactCandidates007.Metadata.orderingStart
abbrev program := PA06A19PrepareCompactCandidates007.program
abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit
abbrev ParentEntry := PA06A19PrepareCompactCandidates007.ParentEntry

def parentTail (tail : List PackingOp) : List PackingOp := RawCandidateParentRAM.programAt parentStart ++ tail
def frontTail (tail : List PackingOp) : List PackingOp := PA06A19PrepareCompactOrdering034Entry.suffix (parentTail tail)

theorem front_program (tail : List PackingOp) :
    PA06A19PrepareCompactOrdering034Entry.frontProgram (frontTail tail) = program tail := rfl

/-- Complete native entry certificate, with no initial table or future
execution premise. The endpoint carries the exact original ParentEntry,
and the extra inverse bound is derived from this execution's Sorted data. -/
theorem parent_native_entry (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length)) :
    ∃ clock ≤ PA06A19PrepareCompactCandidates007.parentClockBound q full,
      let after := natRun (rawIncidenceROM q full) (program tail) clock natInitial
      PrefixSafe (PA06A19PrepareCompactOrdering034Entry.Point q full (frontTail tail))
          (rawIncidenceROM q full) (program tail) natInitial clock ∧
        RegistersFit (indexWidth 32 full.length q) after ∧
        ParentEntry q full after ∧ PA06A19PrepareCompactArrays018.InverseValuesBound q full after := by
  let M := full.length + q + 1
  let nodes := (RawCandidateOrder.retainedCandidateIndices q full).length
  obtain ⟨first, firstBound, previousPoints, previousRegisters, sorted, previousZero⟩ :=
    PA06A19PrepareCompactOrdering034Entry.sorted_native_entry q full (parentTail tail) hlaminar hend
  let before := natRun (rawIncidenceROM q full) (program tail) first natInitial
  let sortedClock := first + RawCandidateOrderingRAM.totalSteps M
  let sortedState := natRun (rawIncidenceROM q full) (program tail) sortedClock natInitial
  have hs : RawCandidateOrderingRAM.Sorted q full 16 orderingStart before sortedState := sorted
  let order := RawCandidateParentRAM.observedOrder q full 16 sortedState
  let inverse := RawCandidateParentRAM.observedInverse q full 16 sortedState
  let parentSteps := RawCandidateParentRAM.totalSteps full.length q nodes order
  have tables := RawCandidateParentRAM.InputTables.of_sorted q full 16 orderingStart before sortedState hs hq
  have inverseFits := PA06A19PrepareCompactParents035Data.inverseFits_of_sorted q full orderingStart before sortedState hs
  have oldInverse := PA06A19PrepareCompactArrays018.inverseValuesBound_of_sorted hs
  have pc : sortedState.pc = 5 * parentStart := hs.returned.pc
  have active : sortedState.halted = false := hs.returned.active
  have slice := PA06A19PrepareCompactCandidates007.parent_slice tail
  have pend : Fits (indexWidth 32 full.length q) (5 * (parentStart + 361)) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 5 slice.1) hend
  have safe := PA06A19PrepareCompactParents035Loop.parents_nat_safe q full (program tail) parentStart
    slice.1 slice.2 nodes order inverse sortedState tables inverseFits pc active previousRegisters pend
  have native := RawCandidateParentRAM.parents q full (program tail) parentStart slice.1 slice.2
    16 nodes order inverse sortedState (by decide) tables pc active
  have prepared := RawCandidateParentRAM.parents_prepared q full hq (program tail) parentStart
    slice.1 slice.2 16 orderingStart before sortedState (by decide) hs pc active
  dsimp only at native prepared
  let finalState := natRun (rawIncidenceROM q full) (program tail) parentSteps sortedState
  have finalRun : natRun (rawIncidenceROM q full) (program tail) (sortedClock + parentSteps) natInitial = finalState :=
    natRun_add _ _ _ _ _
  have parentPoints : PrefixSafe (PA06A19PrepareCompactOrdering034Entry.Point q full (frontTail tail))
      (rawIncidenceROM q full) (program tail) sortedState parentSteps := by
    intro count hc
    have point := safe.1 count hc
    have pcFit := point.pcFits pend
    obtain ⟨registers, offset, hoff, position, a, op, decoded, access⟩ := point
    exact PA06A19PrepareCompactOrdering034Entry.point_of_decoded q full (frontTail tail) _ registers pcFit a
      (parentStart + offset) (by
        change PA06A19PrepareCompactCandidates007.parentStart + offset <
          (PA06A19PrepareCompactCandidates007.program tail).length
        omega) position op decoded access
  have wholePoints : PrefixSafe (PA06A19PrepareCompactOrdering034Entry.Point q full (frontTail tail))
      (rawIncidenceROM q full) (program tail) natInitial (sortedClock + parentSteps) :=
    PrefixSafe.add _ _ _ _ _ _ previousPoints parentPoints
  have entry : ParentEntry q full finalState := by
    refine ⟨?_, prepared, ?_, native.2.2.2.2.2, ?_⟩
    · refine ⟨order, inverse, native.1, ?_⟩
      exact RawCandidateParentRAM.observedOrder_support_of_sorted q full 16 orderingStart before sortedState hs hq
    · exact native.2.2.2.2.1
    · intro address haddress
      have hn : nodes ≤ M := tables.nodes_le
      have hprotected : RawCandidateParentRAM.ProtectedAddress 16 M nodes address := by
        refine ⟨by unfold PA06A19PrepareCompactCandidates007.workspaceEnd at haddress; omega,
          by unfold PA06A19PrepareCompactCandidates007.workspaceEnd at haddress; omega,
          by unfold PA06A19PrepareCompactCandidates007.workspaceEnd at haddress; omega,
          by unfold PA06A19PrepareCompactCandidates007.workspaceEnd at haddress; omega, Or.inr ?_⟩
        rw [RawCandidateParentRAM.parentSlot_eq]
        unfold PA06A19PrepareCompactCandidates007.workspaceEnd at haddress
        omega
      rw [native.2.2.2.1 address hprotected]
      exact previousZero address (by unfold PA06A19PrepareCompactCandidates007.workspaceEnd at haddress; omega)
  have newInverse : PA06A19PrepareCompactArrays018.InverseValuesBound q full finalState := by
    intro index hi
    rw [native.1.inverses index hi]
    exact oldInverse index hi
  have cost := RawCandidateParentRAM.totalSteps_le full.length q nodes order
  have nodeCount : nodes = (prepareNormalization q full).indexed.nodes.size :=
    (RawCandidateParentRAM.prepared_nodes_eq_retained q full hq).symm
  rw [nodeCount] at cost
  refine ⟨sortedClock + parentSteps, ?_, ?_⟩
  · dsimp only [PA06A19PrepareCompactCandidates007.parentClockBound, sortedClock, parentSteps, M]
    rw [nodeCount]
    omega
  · dsimp only
    rw [finalRun]
    exact ⟨wholePoints, safe.2, entry, newInverse⟩

/-- Physical Word cache fields consumed by the subsequent real header
construction. This includes exact prepared-parent encodings at the
bounded physical addresses, with no wraparound. -/
def WordParents (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q)) : Prop :=
  state.halted = false ∧ state.pc.toNat = 5 * inputStart ∧
    (state.heap (BitVec.ofNat _ 8)).toNat = 16 ∧
    (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1 ∧
    (state.heap (BitVec.ofNat _ (RawCandidateParentRAM.nodeCountAddress 16 (full.length + q + 1)))).toNat =
      (prepareNormalization q full).indexed.nodes.size ∧
    ∀ child : (prepareNormalization q full).indexed.NodeId,
      (state.heap (BitVec.ofNat _ (RawCandidateParentRAM.parentSlot 16 (full.length + q + 1) child.val))).toNat =
        encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get child)

theorem wordParents_of_native (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (state : NatState) (entry : ParentEntry q full state)
    (pcFit : Fits (indexWidth 32 full.length q) (5 * inputStart)) :
    WordParents q full (state.toWord (indexWidth 32 full.length q)) := by
  let bits := indexWidth 32 full.length q
  have heapWord (address value : Nat) (ha : Fits bits address) (hv : Fits bits value)
      (heq : state.heap address = value) :
      ((state.toWord bits).heap (BitVec.ofNat bits address)).toNat = value := by
    change (BitVec.ofNat bits (state.heap (BitVec.ofNat bits address).toNat)).toNat = value
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, heq, Nat.mod_eq_of_lt hv]
  have small (value : Nat) (hv : value ≤ 16) : Fits bits value :=
    PA06A19PrepareCompactMacros014.small_constant_fits full.length q value hv
  have countFit : Fits bits (full.length + q + 1) :=
    PA06A19PrepareCompactArrays018.value_le_count_fits full.length q _ le_rfl
  have sizeLe : (prepareNormalization q full).indexed.nodes.size ≤ full.length + q + 1 := prepared_indexed_size_le q full
  have addressFit (address : Nat) (ha : address < PA06A19PrepareCompactCandidates007.workspaceEnd full.length q) :
      Fits bits address := by
    apply lt_trans ha
    apply lt_of_le_of_lt _ (PA06A19PrepareCompactArrays018.linearLimit_fits full.length q)
    change PA06A19PrepareCompactCandidates007.workspaceEnd full.length q ≤ linearLimit full.length q
    unfold PA06A19PrepareCompactCandidates007.workspaceEnd linearLimit PA06A19PrepareCompactWord008.linearLimit
    omega
  refine ⟨entry.active, ?_, ?_, ?_, ?_, ?_⟩
  · change (BitVec.ofNat bits state.pc).toNat = _
    rw [entry.pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit]
  · exact heapWord 8 16 (small 8 (by decide)) (small 16 le_rfl) entry.base_cell
  · exact heapWord 16 (full.length + q + 1) (small 16 le_rfl) countFit entry.count_cell
  · exact heapWord _ _ (addressFit _ (by
      unfold RawCandidateParentRAM.nodeCountAddress RawCandidateOrderingRAM.arraySlot
        PA06A19PrepareCompactCandidates007.workspaceEnd
      omega)) (sizeLe.trans_lt countFit) (entry.node_count hq)
  · intro child
    exact heapWord _ _ (addressFit _ (PA06A19PrepareCompactCandidates007.parent_address_lt q full child))
      (((UniformNormalizationRAM.encodedNode_le _ _).trans sizeLe).trans_lt countFit) (entry.parents child)

/-- Same actual controllerInput run from the original initial state to
the complete prepared-parent cache. Every strict clock is physically
safe; no separate raw run, PC restart, old width bound or metadata input
is supplied. The only residual qualifiers concern the actual code. -/
theorem parent_entry (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (initialUsed : Finset (Fin q)) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode (program tail))) :
    ∃ clock ≤ PA06A19PrepareCompactCandidates007.parentClockBound q full,
      let native := natRun (rawIncidenceROM q full) (program tail) clock natInitial
      let actual := packingRun (CompactControllerClaims.controllerInput q full initialUsed) (program tail) clock
        (natInitial.toWord (indexWidth 32 full.length q))
      ParentEntry q full native ∧ PA06A19PrepareCompactArrays018.InverseValuesBound q full native ∧
        RegistersFit (indexWidth 32 full.length q) native ∧ WordParents q full actual ∧
        (∀ count ≤ clock,
          packingRun (CompactControllerClaims.controllerInput q full initialUsed) (program tail) count
            (natInitial.toWord (indexWidth 32 full.length q)) =
              (natRun (rawIncidenceROM q full) (program tail) count natInitial).toWord (indexWidth 32 full.length q)) ∧
        ∀ count < clock,
          let current := packingRun (CompactControllerClaims.controllerInput q full initialUsed) (program tail) count
            (natInitial.toWord (indexWidth 32 full.length q))
          current.halted = false ∧ current.pc.toNat + 4 < (packingCode (program tail)).length ∧
            ∃ op, PackingOp.decode (fetch (program tail) current) = some op ∧
              packingAccessFits (CompactControllerClaims.controllerInput q full initialUsed) (linearLimit full.length q) current op := by
  obtain ⟨clock, bound, points, registers, entry, inverse⟩ := parent_native_entry q full tail hq hlaminar hend
  have words := PA06A19PrepareCompactOrdering034Entry.word_prefix_of_points q full (frontTail tail) initialUsed clock points hwords
  rw [front_program tail] at words
  have pcFit : Fits (indexWidth 32 full.length q) (5 * inputStart) := by
    apply lt_of_le_of_lt _ hend
    have slice := PA06A19PrepareCompactCandidates007.parent_slice tail
    exact Nat.mul_le_mul_left 5 slice.1
  refine ⟨clock, bound, entry, inverse, registers, ?_, words.1, words.2⟩
  rw [words.1 clock le_rfl]
  exact wordParents_of_native q full hq _ entry pcFit

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Entry

