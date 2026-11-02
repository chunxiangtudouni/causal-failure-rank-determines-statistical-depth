module

public import PaperProofs.Structure.RawCandidateConstructorPrefix
public import PaperProofs.Structure.RawCandidateRetentionRAM
public import PaperProofs.Structure.RawCandidateOrderingRAM

/-! The original raw input produces the candidate tables used by the
next machine phase.  Runtime B/M/card/keep are consequences of the actual
checker, initialization, and double-loop run, not extra input data. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateMetadataPrefix

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM

def retentionStart : Nat := checker.length + 18

def program (tail : List PackingOp) : List PackingOp :=
  RawCandidateConstructorPrefix.program (RawCandidateRetentionRAM.programAt retentionStart ++ tail)

def front (tail : List PackingOp) : List PackingOp :=
  checker ++ dispatcherGate (RawCandidateWorkspaceInit.program ++
    (RawCandidateRetentionRAM.programAt retentionStart ++ tail)).length ++
      RawCandidateWorkspaceInit.program

theorem front_length (tail : List PackingOp) : (front tail).length = retentionStart := by
  simp only [front, List.length_append, dispatcherGate_length,
    RawCandidateWorkspaceInit.program_length, retentionStart]

theorem program_eq (tail : List PackingOp) :
    front tail ++ RawCandidateRetentionRAM.programAt (front tail).length ++ tail = program tail := by
  rw [front_length]
  simp only [front, program, RawCandidateConstructorPrefix.program, dispatcherProgram, List.append_assoc]

theorem retained_entry (tail : List PackingOp) (q : Nat)
    (full : List (Finset (Fin q))) (hlaminar : LaminarSchedule full) :
    let base := RawCandidateWorkspaceInit.workspaceBase full.length q
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
  let base := RawCandidateWorkspaceInit.workspaceBase full.length q
  have hlarge : 16 ≤ base := RawCandidateWorkspaceInit.workspaceBase_ge full.length q
  obtain ⟨first, hfirst, hactive, hpc, _hvalue, hbase, hcount, hzero⟩ :=
    RawCandidateConstructorPrefix.initialized_entry
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
    let base := RawCandidateWorkspaceInit.workspaceBase full.length q
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
  let base := RawCandidateWorkspaceInit.workspaceBase full.length q
  let count := full.length + q + 1
  have hlarge : 16 ≤ base := RawCandidateWorkspaceInit.workspaceBase_ge full.length q
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

end PaperProofs.Structure.LaminarTree.RawCandidateMetadataPrefix
