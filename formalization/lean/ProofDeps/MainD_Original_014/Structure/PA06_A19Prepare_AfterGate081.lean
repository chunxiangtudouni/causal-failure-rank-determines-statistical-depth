module

public import Structure.PA06_A19Prepare_AfterGate081_Sorted

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED real compact continuation after the early gate and compact
initializer.  The supplied whole program is never replaced by the old raw
program.  Retention, sorting and parents share one cumulative actual clock. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterGate081

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

abbrev ParentEntry := PA06A19PrepareCompactCandidates007.ParentEntry

def clockBound (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  retentionClock full.length q + orderingClock full.length q +
    512 * ((prepareNormalization q full).indexed.nodes.size + 1) * (full.length + q + 2) * (q + 1)

theorem add_front_clock_le (q : Nat) (full : List (Finset (Fin q))) (frontClock : Nat)
    (bound : frontClock <= checkerSteps full.length q + 17) :
    frontClock + clockBound q full <= PA06A19PrepareCompactCandidates007.parentClockBound q full := by
  unfold clockBound PA06A19PrepareCompactCandidates007.parentClockBound retentionClock orderingClock
  omega

/-- All retained card/ord/parent facts are outputs of the same real run.
The input contains only the compact initializer's current heap/register/PC
facts, three actual code slices, and the containing-code PC room. -/
theorem after_gate_native (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (whole : List PackingOp) (retention : RetentionAt whole) (ordering : OrderingAt whole)
    (parents : ParentsAt whole) (before : NatState) (initialized : Initialized q full before)
    (hend : Fits (bits q full) (5 * whole.length)) :
    ∃ clock ≤ clockBound q full,
      let after := natRun (rawIncidenceROM q full) whole clock before
      PrefixSafe (Point q full whole) (rawIncidenceROM q full) whole before clock ∧
        RegistersFit (bits q full) after ∧ ParentEntry q full after ∧
        PA06A19PrepareCompactArrays018.InverseValuesBound q full after ∧
        PA06A19PrepareCompactParents035Ord.OrdDataNat q full after ∧
        (∀ candidate : Fin (full.length + q + 1),
          after.heap (PA06A19PrepareCompactParents035Cards.cardSlot full.length q candidate.val) =
            RawCandidateStableOrder.candidateCard q full candidate.val) ∧
        after.pc = 5 * inputStart ∧ after.halted = false := by
  let rom := rawIncidenceROM q full
  let M := full.length + q + 1
  let rtime := retentionClock full.length q
  let stime := orderingClock full.length q
  let sortedClock := rtime + stime
  let retained := natRun rom whole rtime before
  let sorted := natRun rom whole sortedClock before
  have previous := retained_sorted q full whole retention ordering before initialized hend
  dsimp only at previous
  rcases previous with ⟨previousPoints, previousRegisters, hs, previousZero⟩
  have sortedData : RawCandidateOrderingRAM.Sorted q full 16 orderingStart retained sorted := hs
  let nodes := (RawCandidateOrder.retainedCandidateIndices q full).length
  let order := RawCandidateParentRAM.observedOrder q full 16 sorted
  let inverse := RawCandidateParentRAM.observedInverse q full 16 sorted
  let parentSteps := RawCandidateParentRAM.totalSteps full.length q nodes order
  have tables := RawCandidateParentRAM.InputTables.of_sorted q full 16 orderingStart retained sorted sortedData hq
  have inverseFits := PA06A19PrepareCompactParents035Data.inverseFits_of_sorted q full orderingStart retained sorted sortedData
  have oldInverse := PA06A19PrepareCompactArrays018.inverseValuesBound_of_sorted sortedData
  have pc : sorted.pc = 5 * parentStart := sortedData.returned.pc
  have active : sorted.halted = false := sortedData.returned.active
  have pend : Fits (bits q full) (5 * (parentStart + 361)) :=
    (Nat.mul_le_mul_left 5 parents.1).trans_lt hend
  have safe := PA06A19PrepareCompactParents035Loop.parents_nat_safe q full whole parentStart
    parents.1 parents.2 nodes order inverse sorted tables inverseFits pc active previousRegisters pend
  have native := RawCandidateParentRAM.parents q full whole parentStart parents.1 parents.2
    16 nodes order inverse sorted (by decide) tables pc active
  have prepared := RawCandidateParentRAM.parents_prepared q full hq whole parentStart parents.1 parents.2
    16 orderingStart retained sorted (by decide) sortedData pc active
  dsimp only at native prepared
  let finalState := natRun rom whole parentSteps sorted
  have finalRun : natRun rom whole (sortedClock + parentSteps) before = finalState :=
    natRun_add rom whole sortedClock parentSteps before
  have parentPoints : PrefixSafe (Point q full whole) rom whole sorted parentSteps := by
    intro count hc
    obtain ⟨registers, offset, hoff, position, a, op, decoded, access⟩ := safe.1 count hc
    exact point_of_local q full whole parentStart 361 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      parents.1 pend _ registers a offset hoff position op decoded access
  have wholePoints : PrefixSafe (Point q full whole) rom whole before (sortedClock + parentSteps) :=
    PrefixSafe.add (Point q full whole) rom whole before sortedClock parentSteps previousPoints parentPoints
  have entry : ParentEntry q full finalState := by
    refine ⟨?_, prepared, ?_, native.2.2.2.2.2, ?_⟩
    · refine ⟨order, inverse, native.1, ?_⟩
      exact RawCandidateParentRAM.observedOrder_support_of_sorted q full 16 orderingStart retained sorted sortedData hq
    · simpa only [PA06A19PrepareCompactCandidates007.inputStart_eq] using native.2.2.2.2.1
    · intro address haddress
      have hn : nodes <= M := tables.nodes_le
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
  have ordinal : PA06A19PrepareCompactParents035Ord.OrdDataNat q full finalState :=
    PA06A19PrepareCompactParents035Ord.ord_data_of_sorted_tables q full orderingStart retained sorted finalState hq sortedData native.1
  have cards (candidate : Fin (full.length + q + 1)) :
      finalState.heap (PA06A19PrepareCompactParents035Cards.cardSlot full.length q candidate.val) =
        RawCandidateStableOrder.candidateCard q full candidate.val :=
    native.1.cards candidate.val candidate.isLt
  have cost : parentSteps ≤ 512 * (nodes + 1) * (full.length + q + 2) * (q + 1) :=
    RawCandidateParentRAM.totalSteps_le full.length q nodes order
  have nodeCount : nodes = (prepareNormalization q full).indexed.nodes.size :=
    (RawCandidateParentRAM.prepared_nodes_eq_retained q full hq).symm
  refine ⟨sortedClock + parentSteps, ?_, ?_⟩
  · change rtime + stime + parentSteps <= rtime + stime + _
    apply Nat.add_le_add_left
    calc
      parentSteps ≤ 512 * (nodes + 1) * (full.length + q + 2) * (q + 1) := cost
      _ = 512 * ((prepareNormalization q full).indexed.nodes.size + 1) *
          (full.length + q + 2) * (q + 1) := by rw [nodeCount]
  · dsimp only
    rw [finalRun]
    refine ⟨wholePoints, safe.2, entry, newInverse, ordinal, cards, ?_, entry.active⟩
    simpa only [PA06A19PrepareCompactCandidates007.inputStart_eq] using entry.pc

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterGate081
