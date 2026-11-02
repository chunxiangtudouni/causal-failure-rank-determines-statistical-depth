module

public import PaperProofs.Structure.RawCandidateWorkspaceInit
public import PaperProofs.Structure.RawIncidenceWorkspace

/-! The real checker, gate, and workspace initialization in one fixed
instruction stream.  The arbitrary tail is never assumed correct, safe,
or terminating.  Only the executed prefix is described here. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateConstructorPrefix

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM

def program (tail : List PackingOp) : List PackingOp :=
  dispatcherProgram (RawCandidateWorkspaceInit.program ++ tail)

theorem initialized_entry (tail : List PackingOp) (q : Nat)
    (full : List (Finset (Fin q))) (hlaminar : LaminarSchedule full) :
    ∃ clock : Nat, clock ≤ checkerSteps full.length q + 17 ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).halted = false ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).pc =
        5 * (checker.length + 18) ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).register .value = 1 ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap 8 =
        RawCandidateWorkspaceInit.workspaceBase full.length q ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap
          (RawCandidateWorkspaceInit.workspaceBase full.length q) =
        RawCandidateWorkspaceInit.candidateCount full.length q ∧
      ∀ address : Nat, 8 ≤ address → address ≠ 8 →
        address ≠ RawCandidateWorkspaceInit.workspaceBase full.length q →
          (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap address = 0 := by
  let front := checker ++ dispatcherGate (RawCandidateWorkspaceInit.program ++ tail).length
  have hfront : front.length = checker.length + 2 := by
    simp only [front, List.length_append, dispatcherGate_length]
  have hprogram : front ++ RawCandidateWorkspaceInit.program ++ tail = program tail := by
    simp only [front, program, dispatcherProgram, List.append_assoc]
  obtain ⟨clock, hclock, hactive, hpc, hvalue, hzero⟩ :=
    dispatcher_constructor_entry (RawCandidateWorkspaceInit.program ++ tail) q full hlaminar
  let before := natRun (rawIncidenceROM q full) (program tail) clock natInitial
  have hbeforepc : before.pc = 5 * front.length := by
    rw [hfront]
    exact hpc
  have hinit := RawCandidateWorkspaceInit.initialize_append q full front tail before hbeforepc hactive
  rw [hprogram] at hinit
  have hinit' : RawCandidateWorkspaceInit.Initialized full.length q front.length before
      (natRun (rawIncidenceROM q full) (program tail) (clock + 16) natInitial) := by
    simpa only [before, natRun_add] using hinit
  refine ⟨clock + 16, by omega, hinit'.active, ?_, hinit'.value.trans hvalue,
    hinit'.base_cell, hinit'.count_cell, ?_⟩
  · rw [hinit'.pc, hfront]
  · intro address haddress h8 hbase
    rw [hinit'.heap_frame address h8 hbase]
    exact hzero address haddress

/-- A nonlaminar input never executes the initialization or the tail. -/
theorem rejects (tail : List PackingOp) (q : Nat) (full : List (Finset (Fin q)))
    (hnot : ¬ LaminarSchedule full) :
    ∃ clock : Nat, clock ≤ checkerSteps full.length q + 2 ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).halted = true ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).register .value = 0 := by
  obtain ⟨count, hcount, _hprefix, _hactive, _hheap, _hvalue, hreject, _haccept, _hempty⟩ :=
    checker_dispatcher_boundary (RawCandidateWorkspaceInit.program ++ tail) q full
  obtain ⟨_hpc, _hflag, hhalt, hzero, _hframe⟩ := hreject hnot
  exact ⟨count + 3, hcount, hhalt, hzero⟩

end PaperProofs.Structure.LaminarTree.RawCandidateConstructorPrefix
