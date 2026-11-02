module

public import Structure.PA06_A19Prepare_CompactParents035Entry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Add the actual ord source data omitted by the weak ParentEntry ABI.
Membership is obtained from the real Sorted.support_at_position, then
preserved by the original parent's actual InputTables transport. This
module only recomposes the existing native entry and real Word prefix;
it does not reprove sorting/parents or add a candidate oracle. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Ord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

abbrev program := PA06A19PrepareCompactParents035Entry.program
abbrev parentStart := PA06A19PrepareCompactParents035Entry.parentStart
abbrev inputStart := PA06A19PrepareCompactParents035Entry.inputStart
abbrev orderingStart := PA06A19PrepareCompactParents035Entry.orderingStart
abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit
abbrev ParentEntry := PA06A19PrepareCompactCandidates007.ParentEntry
abbrev WordParents := PA06A19PrepareCompactParents035Entry.WordParents
abbrev parentTail := PA06A19PrepareCompactParents035Entry.parentTail
abbrev frontTail := PA06A19PrepareCompactParents035Entry.frontTail

def ordSlot (N q node : Nat) : Nat := RawCandidateOrderingRAM.arraySlot 16 (N + q + 1) 2 node

def OrdDataNat (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop :=
  ∀ node : (prepareNormalization q full).indexed.NodeId,
    let candidate := state.heap (ordSlot full.length q node.val)
    candidate ∈ RawCandidateOrder.retainedCandidateIndices q full ∧ candidate < full.length + q + 1 ∧
      RawCandidateParents.candidateSupport q full candidate = (prepareNormalization q full).indexed.decode node

/-- Data-only physical ABI: the real cached word, its candidate bound,
its retained membership, and its interpretation as the prepared node. -/
def OrdData (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q)) : Prop :=
  ∀ node : (prepareNormalization q full).indexed.NodeId,
    let candidate := (state.heap (BitVec.ofNat _ (ordSlot full.length q node.val))).toNat
    candidate ∈ RawCandidateOrder.retainedCandidateIndices q full ∧ candidate < full.length + q + 1 ∧
      RawCandidateParents.candidateSupport q full candidate = (prepareNormalization q full).indexed.decode node

theorem ord_data_of_sorted_tables (q : Nat) (full : List (Finset (Fin q)))
    (sortStart : Nat) (before sorted after : NatState) (hq : 0 < q)
    (hs : RawCandidateOrderingRAM.Sorted q full 16 sortStart before sorted)
    (tables : RawCandidateParentRAM.InputTables q full 16 (RawCandidateOrder.retainedCandidateIndices q full).length
      (RawCandidateParentRAM.observedOrder q full 16 sorted) (RawCandidateParentRAM.observedInverse q full 16 sorted) after) :
    OrdDataNat q full after := by
  intro node
  have hn : node.val < (RawCandidateOrder.retainedCandidateIndices q full).length := by
    rw [← RawCandidateParentRAM.prepared_nodes_eq_retained q full hq]
    exact node.isLt
  have stored := tables.ordered node.val hn
  change after.heap (ordSlot full.length q node.val) = _ at stored
  dsimp only
  rw [stored]
  refine ⟨?_, tables.order_valid node.val hn, ?_⟩
  · obtain ⟨candidate, member, atPosition, _rank, _support⟩ :=
      RawCandidateOrderingRAM.Sorted.support_at_position q full 16 sortStart before sorted hs hq node.val hn
    change sorted.heap (RawCandidateOrderingRAM.arraySlot 16 (full.length + q + 1) 2 node.val) ∈ _
    rw [atPosition]
    exact member
  · exact RawCandidateParentRAM.observedOrder_support_of_sorted q full 16 sortStart before sorted hs hq node

theorem ord_address_fits (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) :
    Fits (indexWidth 32 full.length q) (ordSlot full.length q node.val) := by
  have hn : node.val < full.length + q + 1 := lt_of_lt_of_le node.isLt (prepared_indexed_size_le q full)
  have address := PA06A19PrepareCompactCandidates007.candidate_array_address_lt full.length q 2 node.val (by decide) hn
  apply lt_trans address
  apply lt_of_le_of_lt _ (PA06A19PrepareCompactArrays018.linearLimit_fits full.length q)
  change PA06A19PrepareCompactCandidates007.workspaceEnd full.length q ≤ linearLimit full.length q
  unfold PA06A19PrepareCompactCandidates007.workspaceEnd linearLimit PA06A19PrepareCompactWord008.linearLimit
  omega

theorem ord_data_toWord (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (data : OrdDataNat q full state) :
    OrdData q full (state.toWord (indexWidth 32 full.length q)) ∧
      ∀ node : (prepareNormalization q full).indexed.NodeId,
        ((state.toWord (indexWidth 32 full.length q)).heap
          (BitVec.ofNat _ (ordSlot full.length q node.val))).toNat =
            RawCandidateParentRAM.observedOrder q full 16 state node.val := by
  have value (node : (prepareNormalization q full).indexed.NodeId) :
      ((state.toWord (indexWidth 32 full.length q)).heap
        (BitVec.ofNat _ (ordSlot full.length q node.val))).toNat = state.heap (ordSlot full.length q node.val) := by
    have bound := (data node).2.1
    have fit := PA06A19PrepareCompactArrays018.value_le_count_fits full.length q _ bound.le
    change (BitVec.ofNat _ (state.heap (BitVec.ofNat (indexWidth 32 full.length q)
      (ordSlot full.length q node.val)).toNat)).toNat = _
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ord_address_fits q full node), Nat.mod_eq_of_lt fit]
  constructor
  · intro node
    dsimp only
    rw [value]
    exact data node
  · intro node
    exact value node

theorem ord_data_frame (q : Nat) (full : List (Finset (Fin q)))
    (before after : WordState (indexWidth 32 full.length q))
    (frame : ∀ address : BitVec (indexWidth 32 full.length q),
      16 ≤ address.toNat → after.heap address = before.heap address)
    (data : OrdData q full before) : OrdData q full after := by
  intro node
  have above : 16 ≤ (BitVec.ofNat (indexWidth 32 full.length q) (ordSlot full.length q node.val)).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ord_address_fits q full node)]
    unfold ordSlot RawCandidateOrderingRAM.arraySlot
    omega
  dsimp only
  rw [frame _ above]
  exact data node

theorem parent_native_entry (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length)) :
    ∃ clock ≤ PA06A19PrepareCompactCandidates007.parentClockBound q full,
      let after := natRun (rawIncidenceROM q full) (program tail) clock natInitial
      PrefixSafe (PA06A19PrepareCompactOrdering034Entry.Point q full (frontTail tail))
          (rawIncidenceROM q full) (program tail) natInitial clock ∧
        RegistersFit (indexWidth 32 full.length q) after ∧
        ParentEntry q full after ∧ PA06A19PrepareCompactArrays018.InverseValuesBound q full after ∧ OrdDataNat q full after := by
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
  have ordinal : OrdDataNat q full finalState :=
    ord_data_of_sorted_tables q full orderingStart before sortedState finalState hq hs native.1
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
    exact ⟨wholePoints, safe.2, entry, newInverse, ordinal⟩



/-- The original same-run parent entry, strengthened only with actual
ord source data and its exact Nat-to-Word transport. All old outputs,
the original clock bound and the physical prefix safety are retained. -/
theorem parent_entry (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (initialUsed : Finset (Fin q)) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode (program tail))) :
    ∃ clock ≤ PA06A19PrepareCompactCandidates007.parentClockBound q full,
      let native := natRun (rawIncidenceROM q full) (program tail) clock natInitial
      let actual := packingRun (CompactControllerClaims.controllerInput q full initialUsed) (program tail) clock
        (natInitial.toWord (indexWidth 32 full.length q))
      ParentEntry q full native ∧ PA06A19PrepareCompactArrays018.InverseValuesBound q full native ∧
        RegistersFit (indexWidth 32 full.length q) native ∧ WordParents q full actual ∧ OrdData q full actual ∧
        (∀ node : (prepareNormalization q full).indexed.NodeId,
          (actual.heap (BitVec.ofNat _ (ordSlot full.length q node.val))).toNat =
            RawCandidateParentRAM.observedOrder q full 16 native node.val) ∧
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
  obtain ⟨clock, bound, points, registers, entry, inverse, ordinary⟩ := parent_native_entry q full tail hq hlaminar hend
  have words := PA06A19PrepareCompactOrdering034Entry.word_prefix_of_points q full (frontTail tail) initialUsed clock points hwords
  have sameCode : PA06A19PrepareCompactOrdering034Entry.frontProgram (frontTail tail) = program tail :=
    PA06A19PrepareCompactParents035Entry.front_program tail
  rw [sameCode] at words
  have ordinal := ord_data_toWord q full _ ordinary
  have pcFit : Fits (indexWidth 32 full.length q) (5 * inputStart) := by
    apply lt_of_le_of_lt _ hend
    have slice := PA06A19PrepareCompactCandidates007.parent_slice tail
    exact Nat.mul_le_mul_left 5 slice.1
  refine ⟨clock, bound, entry, inverse, registers, ?_, ?_, ?_, words.1, words.2⟩
  · rw [words.1 clock le_rfl]
    exact PA06A19PrepareCompactParents035Entry.wordParents_of_native q full hq _ entry pcFit
  · rw [words.1 clock le_rfl]
    exact ordinal.1
  · rw [words.1 clock le_rfl]
    exact ordinal.2

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Ord

