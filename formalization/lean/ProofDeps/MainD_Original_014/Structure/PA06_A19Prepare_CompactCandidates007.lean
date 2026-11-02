module

public import Structure.PA06_A19Prepare_CompactInit006
public import PaperProofs.Structure.RawCandidateRetentionRAM
public import PaperProofs.Structure.RawCandidateOrderingRAM
public import PaperProofs.Structure.RawCandidateParentRAM
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000

/-! PRIVATE UNCOMPILED positive compact raw candidate prefix.
This reuses the exact generic runtime retention/sort/parent machines at B=16.
No card/keep/order/inverse/parent data or workspace base is an input oracle.
Only a Nat result is claimed; old Word proofs pinning the old B are not reused.
No serializer, packed output, dimension-dependent tree primitive or matrix is
introduced. The arbitrary tail starts after the fixed parent body. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactCandidates007

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM

namespace Metadata

def retentionStart : Nat := checker.length + 18

def program (tail : List PackingOp) : List PackingOp :=
  PA06A19PrepareCompactInit006.program (RawCandidateRetentionRAM.programAt retentionStart ++ tail)

def front (tail : List PackingOp) : List PackingOp :=
  checker ++ dispatcherGate (PA06A19PrepareCompactInit006.initProgram ++
    (RawCandidateRetentionRAM.programAt retentionStart ++ tail)).length ++
      PA06A19PrepareCompactInit006.initProgram

theorem front_length (tail : List PackingOp) : (front tail).length = retentionStart := by
  simp only [front, List.length_append, dispatcherGate_length,
    PA06A19PrepareCompactInit006.initProgram_length, retentionStart]

theorem program_eq (tail : List PackingOp) :
    front tail ++ RawCandidateRetentionRAM.programAt (front tail).length ++ tail = program tail := by
  rw [front_length]
  simp only [front, program, PA06A19PrepareCompactInit006.program, dispatcherProgram, List.append_assoc]

theorem retained_entry (tail : List PackingOp) (q : Nat)
    (full : List (Finset (Fin q))) (hlaminar : LaminarSchedule full) :
    let base := 16
    let count := full.length + q + 1
    ∃ clock : Nat,
      clock ≤ checkerSteps full.length q + 17 + RawCandidateRetentionRAM.totalSteps full.length q ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).halted = false ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).pc = 5 * (retentionStart + 398) ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap 8 = base ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap base = count ∧
      RawCandidateOrderingRAM.InputTables base count (RawCandidateStableOrder.candidateCard q full)
        (RawCandidateOrder.keepCandidate q full)
        (natRun (rawIncidenceROM q full) (program tail) clock natInitial) ∧
      ∀ address : Nat, base + 4 + 2 * count ≤ address →
        (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap address = 0 := by
  dsimp only
  let base := 16
  have hlarge : 16 ≤ base := (by dsimp [base]; omega)
  obtain ⟨first, hfirst, hactive, hpc, _hvalue, hbase, hcount, hzero⟩ :=
    PA06A19PrepareCompactInit006.initialized_entry
      (RawCandidateRetentionRAM.programAt retentionStart ++ tail) q full hlaminar
  let before := natRun (rawIncidenceROM q full) (program tail) first natInitial
  have hbeforepc : before.pc = 5 * (front tail).length := by
    rw [front_length]
    exact hpc
  have hs := RawCandidateRetentionRAM.append_slice (front tail) tail
  have hr := RawCandidateRetentionRAM.retention q full
    (front tail ++ RawCandidateRetentionRAM.programAt (front tail).length ++ tail)
    (front tail).length hs.1 hs.2 base hlarge before hbase hcount hbeforepc hactive
  rw [program_eq tail] at hr
  dsimp only at hr
  have hrun : natRun (rawIncidenceROM q full) (program tail)
      (RawCandidateRetentionRAM.totalSteps full.length q) before =
        natRun (rawIncidenceROM q full) (program tail)
          (first + RawCandidateRetentionRAM.totalSteps full.length q) natInitial := by
    exact (natRun_add _ _ _ _ _).symm
  rw [hrun] at hr
  rcases hr with ⟨hptr, hM, _hindex, harrays, hframe, hpcAfter, hactiveAfter⟩
  refine ⟨first + RawCandidateRetentionRAM.totalSteps full.length q, by omega,
    hactiveAfter, ?_, hptr, hM, ?_, ?_⟩
  · simpa only [front_length] using hpcAfter
  · constructor
    · intro index hi
      have hc := (harrays index hi).1
      simpa only [RawCandidateOrderingRAM.arraySlot, Nat.mul_zero, Nat.add_zero,
        RawCandidateStableOrder.candidateCard, RawCandidateRetentionRAM.cardAddress] using hc
    · intro index hi
      have hk := (harrays index hi).2
      simpa only [base, RawCandidateOrderingRAM.arraySlot, Nat.mul_one,
        RawCandidateRetentionRAM.keepAddress, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
  · intro address haddress
    have hout : RawCandidateRetentionRAM.OutsideWorkspace base (full.length + q + 1) address := by
      exact ⟨by omega, by omega, by omega, by omega, Or.inr haddress⟩
    rw [hframe address hout]
    exact hzero address (by omega) (by omega) (by omega)

def orderingStart : Nat := retentionStart + 398

def orderedProgram (tail : List PackingOp) : List PackingOp :=
  program (RawCandidateOrderingRAM.programAt orderingStart ++ tail)

def orderingFront (tail : List PackingOp) : List PackingOp :=
  front (RawCandidateOrderingRAM.programAt orderingStart ++ tail) ++
    RawCandidateRetentionRAM.programAt retentionStart

theorem orderingFront_length (tail : List PackingOp) : (orderingFront tail).length = orderingStart := by
  simp only [orderingFront, List.length_append, front_length,
    RawCandidateRetentionRAM.programAt_length, orderingStart]

theorem orderedProgram_eq (tail : List PackingOp) :
    orderingFront tail ++ RawCandidateOrderingRAM.programAt (orderingFront tail).length ++ tail =
      orderedProgram tail := by
  rw [orderingFront_length]
  have hh := program_eq (RawCandidateOrderingRAM.programAt orderingStart ++ tail)
  rw [front_length] at hh
  simpa only [orderingFront, orderedProgram, List.append_assoc] using hh

/-- Both input tables consumed by the sorter are materialized by the
same raw-input run. No B/M/card/keep correctness premise remains. -/
theorem sorted_entry (tail : List PackingOp) (q : Nat)
    (full : List (Finset (Fin q))) (hlaminar : LaminarSchedule full) :
    let base := 16
    let count := full.length + q + 1
    ∃ first : Nat,
      first ≤ checkerSteps full.length q + 17 + RawCandidateRetentionRAM.totalSteps full.length q ∧
      RawCandidateOrderingRAM.Sorted q full base orderingStart
        (natRun (rawIncidenceROM q full) (orderedProgram tail) first natInitial)
        (natRun (rawIncidenceROM q full) (orderedProgram tail)
          (first + RawCandidateOrderingRAM.totalSteps count) natInitial) ∧
      ∀ address : Nat, base + 5 + 4 * count ≤ address →
        (natRun (rawIncidenceROM q full) (orderedProgram tail)
          (first + RawCandidateOrderingRAM.totalSteps count) natInitial).heap address = 0 := by
  dsimp only
  let base := 16
  let count := full.length + q + 1
  have hlarge : 16 ≤ base := (by dsimp [base]; omega)
  obtain ⟨first, hfirst, hactive, hpc, hptr, hcount, htables, hzero⟩ :=
    retained_entry (RawCandidateOrderingRAM.programAt orderingStart ++ tail) q full hlaminar
  let before := natRun (rawIncidenceROM q full) (orderedProgram tail) first natInitial
  have hbeforepc : before.pc = 5 * (orderingFront tail).length := by
    rw [orderingFront_length]
    exact hpc
  have hs := RawCandidateOrderingRAM.sort_append q full (orderingFront tail) tail
    base before hlarge hptr hcount htables hbeforepc hactive
  rw [orderedProgram_eq tail] at hs
  have hrun : natRun (rawIncidenceROM q full) (orderedProgram tail)
      (RawCandidateOrderingRAM.totalSteps count) before =
        natRun (rawIncidenceROM q full) (orderedProgram tail)
          (first + RawCandidateOrderingRAM.totalSteps count) natInitial := by
    exact (natRun_add _ _ _ _ _).symm
  rw [hrun, orderingFront_length] at hs
  refine ⟨first, hfirst, hs, ?_⟩
  intro address haddress
  have hprotected : RawCandidateOrderingRAM.ProtectedAddress base count address := by
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro index hi
      unfold RawCandidateOrderingRAM.arraySlot
      omega
    · intro index hi
      unfold RawCandidateOrderingRAM.arraySlot
      omega
    · unfold RawCandidateOrderingRAM.arraySlot
      omega
  rw [hs.frame address hprotected]
  exact hzero address (by omega)

end Metadata

def parentStart : Nat := Metadata.orderingStart + 303

def inputStart : Nat := parentStart + 361

theorem parentStart_eq : parentStart = 845 := by
  simp [parentStart, Metadata.orderingStart, Metadata.retentionStart, checker_length]

theorem inputStart_eq : inputStart = 1206 := by rw [inputStart, parentStart_eq]

def program (tail : List PackingOp) : List PackingOp :=
  Metadata.orderedProgram (RawCandidateParentRAM.programAt parentStart ++ tail)

def parentFront (tail : List PackingOp) : List PackingOp :=
  Metadata.orderingFront (RawCandidateParentRAM.programAt parentStart ++ tail) ++
    RawCandidateOrderingRAM.programAt Metadata.orderingStart

theorem parentFront_length (tail : List PackingOp) : (parentFront tail).length = parentStart := by
  simp only [parentFront, List.length_append, Metadata.orderingFront_length,
    RawCandidateOrderingRAM.programAt_length, parentStart]

theorem parentProgram_eq (tail : List PackingOp) :
    parentFront tail ++ RawCandidateParentRAM.programAt (parentFront tail).length ++ tail = program tail := by
  rw [parentFront_length]
  have h := Metadata.orderedProgram_eq (RawCandidateParentRAM.programAt parentStart ++ tail)
  rw [Metadata.orderingFront_length] at h
  simpa only [parentFront, program, List.append_assoc] using h

theorem parent_slice (tail : List PackingOp) :
    parentStart + 361 ≤ (program tail).length ∧
      ∀ position < 361, (program tail).getD (parentStart + position) RawCandidateParentRAM.paddingOp =
        (RawCandidateParentRAM.programAt parentStart).getD position RawCandidateParentRAM.paddingOp := by
  have h := RawCandidateParentRAM.append_slice (parentFront tail) tail
  rw [parentProgram_eq, parentFront_length] at h
  exact h

/-- Exclusive end of actual retained cache fields: four candidate arrays,
the node count and parent array; scalar slots lie below these. This is a
linear cache address bound, not yet all-prefix Word/physical allocation. -/
def workspaceEnd (N q : Nat) : Nat := 16 + 5 + 5 * (N + q + 1)

def CachedParents (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop :=
  ∀ child : (prepareNormalization q full).indexed.NodeId,
    state.heap (RawCandidateParentRAM.parentSlot 16 (full.length + q + 1) child.val) =
      encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get child)

structure ParentEntry (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop where
  tables : ∃ order inverse : Nat → Nat,
    RawCandidateParentRAM.InputTables q full 16 (RawCandidateOrder.retainedCandidateIndices q full).length
      order inverse state ∧
    ∀ child : (prepareNormalization q full).indexed.NodeId,
      RawCandidateParents.candidateSupport q full (order child.val) =
        (prepareNormalization q full).indexed.decode child
  parents : CachedParents q full state
  pc : state.pc = 5 * inputStart
  active : state.halted = false
  zeroAbove : ∀ address : Nat, workspaceEnd full.length q ≤ address → state.heap address = 0

def parentClockBound (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  checkerSteps full.length q + 17 + RawCandidateRetentionRAM.totalSteps full.length q +
    RawCandidateOrderingRAM.totalSteps (full.length + q + 1) +
      512 * ((prepareNormalization q full).indexed.nodes.size + 1) * (full.length + q + 2) * (q + 1)

/-- Complete SAME raw run through init, retained-card/keep, stable order and
inverse, and original exact prepared-parent cache. q>0 permits N=0. -/
theorem parent_entry (tail : List PackingOp) (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ clock ≤ parentClockBound q full,
      ParentEntry q full (natRun (rawIncidenceROM q full) (program tail) clock natInitial) := by
  let count := full.length + q + 1
  let nodes := (RawCandidateOrder.retainedCandidateIndices q full).length
  obtain ⟨first, hfirst, sorted, hzero⟩ := Metadata.sorted_entry
    (RawCandidateParentRAM.programAt parentStart ++ tail) q full hl
  let before := natRun (rawIncidenceROM q full) (program tail) first natInitial
  let sortedClock := first + RawCandidateOrderingRAM.totalSteps count
  let sortedState := natRun (rawIncidenceROM q full) (program tail) sortedClock natInitial
  have hs : RawCandidateOrderingRAM.Sorted q full 16 Metadata.orderingStart before sortedState := sorted
  let order := RawCandidateParentRAM.observedOrder q full 16 sortedState
  let inverse := RawCandidateParentRAM.observedInverse q full 16 sortedState
  let parentSteps := RawCandidateParentRAM.totalSteps full.length q nodes order
  have ht := RawCandidateParentRAM.InputTables.of_sorted q full 16 _ before sortedState hs hq
  have hpc : sortedState.pc = 5 * parentStart := hs.returned.pc
  have ha : sortedState.halted = false := hs.returned.active
  have hp := RawCandidateParentRAM.parents q full (program tail) parentStart (parent_slice tail).1 (parent_slice tail).2
    16 nodes order inverse sortedState (by decide) ht hpc ha
  have hprepared := RawCandidateParentRAM.parents_prepared q full hq (program tail) parentStart
    (parent_slice tail).1 (parent_slice tail).2 16 Metadata.orderingStart before sortedState (by decide) hs hpc ha
  dsimp only at hp hprepared
  have hrun : natRun (rawIncidenceROM q full) (program tail) parentSteps sortedState =
      natRun (rawIncidenceROM q full) (program tail) (sortedClock + parentSteps) natInitial :=
    (natRun_add _ _ _ _ _).symm
  have hcost := RawCandidateParentRAM.totalSteps_le full.length q nodes order
  have hnodes : nodes = (prepareNormalization q full).indexed.nodes.size :=
    (RawCandidateParentRAM.prepared_nodes_eq_retained q full hq).symm
  rw [hnodes] at hcost
  refine ⟨sortedClock + parentSteps, ?_, ?_⟩
  · dsimp only [parentClockBound, sortedClock, parentSteps, count]
    rw [hnodes]
    omega
  · rw [← hrun]
    refine ⟨?_, hprepared, ?_, hp.2.2.2.2.2, ?_⟩
    · refine ⟨order, inverse, hp.1, ?_⟩
      exact RawCandidateParentRAM.observedOrder_support_of_sorted q full 16 Metadata.orderingStart
        before sortedState hs hq
    · exact hp.2.2.2.2.1
    · intro address haddress
      have hn : nodes ≤ count := ht.nodes_le
      have hcountEq : count = full.length + q + 1 := rfl
      have hprotected : RawCandidateParentRAM.ProtectedAddress 16 count nodes address := by
        refine ⟨by unfold workspaceEnd at haddress; omega, by unfold workspaceEnd at haddress; omega,
          by unfold workspaceEnd at haddress; omega, by unfold workspaceEnd at haddress; omega, Or.inr ?_⟩
        rw [RawCandidateParentRAM.parentSlot_eq]
        unfold workspaceEnd at haddress
        omega
      rw [hp.2.2.2.1 address hprotected]
      exact hzero address (by unfold workspaceEnd at haddress; omega)

/-- These are genuine cached addresses used by the existing runtime bodies;
no capacity matrix is allocated. Full prefix memory safety remains separate. -/
theorem candidate_array_address_lt (N q factor index : Nat) (hf : factor ≤ 3) (hi : index < N + q + 1) :
    RawCandidateOrderingRAM.arraySlot 16 (N + q + 1) factor index < workspaceEnd N q := by
  have hm := Nat.mul_le_mul_right (N + q + 1) hf
  unfold RawCandidateOrderingRAM.arraySlot workspaceEnd
  nlinarith

theorem parent_address_lt (q : Nat) (full : List (Finset (Fin q)))
    (child : (prepareNormalization q full).indexed.NodeId) :
    RawCandidateParentRAM.parentSlot 16 (full.length + q + 1) child.val < workspaceEnd full.length q := by
  have ht := prepared_indexed_size_le q full
  have hc := child.isLt
  rw [RawCandidateParentRAM.parentSlot_eq]
  unfold workspaceEnd
  omega

theorem entry_pc_1206 {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (entry : ParentEntry q full state) : state.pc = 5 * 1206 := by
  simpa only [inputStart_eq] using entry.pc

theorem program_length (tail : List PackingOp) : (program tail).length = 1206 + tail.length := by
  have h := congrArg List.length (parentProgram_eq tail)
  simp only [List.length_append, parentFront_length, RawCandidateParentRAM.programAt_length] at h
  rw [parentStart_eq] at h
  omega

theorem ParentEntry.base_cell {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (entry : ParentEntry q full state) : state.heap 8 = 16 := by
  obtain ⟨order, inverse, ht, _⟩ := entry.tables
  exact ht.base_cell

theorem ParentEntry.count_cell {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (entry : ParentEntry q full state) : state.heap 16 = full.length + q + 1 := by
  obtain ⟨order, inverse, ht, _⟩ := entry.tables
  exact ht.count_cell

theorem ParentEntry.node_count {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (entry : ParentEntry q full state) (hq : 0 < q) :
    state.heap (RawCandidateParentRAM.nodeCountAddress 16 (full.length + q + 1)) =
      (prepareNormalization q full).indexed.nodes.size := by
  obtain ⟨order, inverse, ht, _⟩ := entry.tables
  exact ht.node_count.trans (RawCandidateParentRAM.prepared_nodes_eq_retained q full hq).symm

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactCandidates007
