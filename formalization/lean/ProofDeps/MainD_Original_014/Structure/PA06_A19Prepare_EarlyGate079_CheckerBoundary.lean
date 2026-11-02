module

public import Structure.PA06_A19Prepare_EarlyGate079_Positive
public import Structure.PA06_A19Prepare_EarlyGate079_Control
public import Structure.PA06_A19Prepare_EarlyGate079_CodeAgreement
public import PaperProofs.Structure.RawIncidenceCheckerBoundary
public import PaperProofs.Structure.RawIncidenceWorkspace

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED positive checker boundary in the patched whole code.
The actual original checker witness supplies its own body bound and append
certificate. The proved control invariant discharges all later code-change
steps. No new original-caller run/safety assumption or clock is introduced. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawIncidenceLaminarRAM RawTreePreprocessingClaims RawIncidenceScanSafety

theorem old_prefix_formula (rom : PhysicalROM) (count : Nat) (bound : count ≤ 17) :
    natRun rom checker count natInitial =
      runOps rom ((oldInitialLead ++ [outerBranch]).take count) natInitial := by
  have code : ∀ position (hp : position < oldInitialLead.length),
      checker[0 + position]'(by rw [checker_length]; rw [oldInitialLead_length] at hp; omega) =
        oldInitialLead[position] := by
    intro position hp
    rw [oldInitialLead_length] at hp
    interval_cases position <;> rfl
  exact natRun_segment_prefix rom checker oldInitialLead outerBranch 0
    (by rw [oldInitialLead_length, checker_length]; omega) code (by rfl)
    oldInitialLead_noJump natInitial rfl rfl count bound

theorem old_pc_before_seventeen (rom : PhysicalROM) (count : Nat) (bound : count < 17) :
    (natRun rom checker count natInitial).pc = 5 * count := by
  have within : count ≤ oldInitialLead.length := by rw [oldInitialLead_length]; omega
  rw [old_prefix_formula rom count bound.le, List.take_append_of_le_length within]
  have straight : ∀ op ∈ oldInitialLead.take count, NoJump op := by
    intro op member
    exact oldInitialLead_noJump op (List.mem_of_mem_take member)
  have pc := runOps_pc rom (oldInitialLead.take count) natInitial straight
  rw [List.length_take_of_le within] at pc
  simpa only [natInitial, Nat.zero_add] using pc

theorem old_control_seventeen (rom : PhysicalROM) (N q handlerPC : Nat)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (hq : 0 < q) :
    (natRun rom checker 17 natInitial).pc = (if N = 0 then 630 else 85) ∧
      (natRun rom checker 17 natInitial).halted = false := by
  have same := positive_seventeen_eq rom q handlerPC [] headerQ hq
  have control := positive_seventeen_control rom N q handlerPC [] headerN headerQ hq
  simp only [List.append_nil] at same control
  rw [same] at control
  exact control

theorem checker_patch_eq_after_seventeen (rom : PhysicalROM) (N q handlerPC : Nat)
    (rest : List PackingOp) (cutoff count : Nat)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (hq : 0 < q)
    (oldPrefixes : ∀ clock ≤ cutoff,
      natRun rom (checker ++ rest) clock natInitial = natRun rom checker clock natInitial)
    (oldBody : ∀ clock < cutoff,
      (natRun rom checker clock natInitial).pc < 5 * checker.length)
    (lower : 17 ≤ count) (upper : count ≤ cutoff) :
    natRun rom (program handlerPC (checker ++ rest)) count natInitial =
      natRun rom checker count natInitial := by
  let before := natRun rom (checker ++ rest) 17 natInitial
  have firstPoint : AboveHead (natRun rom checker 17 natInitial) :=
    above_head_of_seventeen_pc N _ (old_control_seventeen rom N q handlerPC headerN headerQ hq).1
  have window : ∀ clock < count - 17, ∃ index, 10 ≤ index ∧ index < (checker ++ rest).length ∧
      (natRun rom (checker ++ rest) clock before).pc = 5 * index := by
    intro clock bound
    have point := above_head_run rom _ firstPoint clock
    have shifted : natRun rom checker clock (natRun rom checker 17 natInitial) =
        natRun rom checker (17 + clock) natInitial := (natRun_add _ _ _ _ _).symm
    rw [shifted] at point
    obtain ⟨index, lo, _hi, control⟩ := point
    have proper : 17 + clock < cutoff := by omega
    have below : (natRun rom checker (17 + clock) natInitial).pc < 630 := by
      simpa only [checker_length] using oldBody (17 + clock) proper
    have strict : index < 126 := by have pc := control.1; omega
    have same : natRun rom (checker ++ rest) clock before =
        natRun rom checker (17 + clock) natInitial := by
      calc
        _ = natRun rom (checker ++ rest) (17 + clock) natInitial := (natRun_add _ _ _ _ _).symm
        _ = _ := oldPrefixes (17 + clock) (by omega)
    refine ⟨index, lo, ?_, ?_⟩
    · simp only [List.length_append, checker_length]
      omega
    · rw [same]
      exact control.1
  have replay := natRun_of_old_window rom handlerPC (checker ++ rest) before (count - 17) window
  have common := positive_seventeen_eq rom q handlerPC rest headerQ hq
  have clockEq : count = 17 + (count - 17) := by omega
  have newSplit : natRun rom (program handlerPC (checker ++ rest)) count natInitial =
      natRun rom (program handlerPC (checker ++ rest)) (count - 17)
        (natRun rom (program handlerPC (checker ++ rest)) 17 natInitial) := by
    calc
      _ = natRun rom (program handlerPC (checker ++ rest)) (17 + (count - 17)) natInitial :=
        congrArg (fun clock => natRun rom (program handlerPC (checker ++ rest)) clock natInitial) clockEq
      _ = _ := natRun_add _ _ _ _ _
  have oldSplit : natRun rom (checker ++ rest) count natInitial =
      natRun rom (checker ++ rest) (count - 17) before := by
    calc
      _ = natRun rom (checker ++ rest) (17 + (count - 17)) natInitial :=
        congrArg (fun clock => natRun rom (checker ++ rest) clock natInitial) clockEq
      _ = _ := natRun_add _ _ _ _ _
  calc
    _ = _ := newSplit
    _ = natRun rom (program handlerPC (checker ++ rest)) (count - 17) before :=
      congrArg (fun state => natRun rom (program handlerPC (checker ++ rest)) (count - 17) state) common
    _ = natRun rom (checker ++ rest) (count - 17) before := replay
    _ = natRun rom (checker ++ rest) count natInitial := oldSplit.symm
    _ = _ := oldPrefixes count upper

theorem patched_checker_boundary (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (handlerPC : Nat) (rest : List PackingOp) :
    ∃ count, 17 ≤ count ∧ count + 1 ≤ checkerSteps full.length q ∧
      let rom := rawIncidenceROM q full
      let after := natRun rom (program handlerPC (checker ++ rest)) count natInitial
      after = natRun rom checker count natInitial ∧ after.halted = false ∧
      after.pc = 630 ∧ after.register .value ≤ 1 ∧
      (after.register .value = 1 ↔ LaminarSchedule full) ∧
      (∀ address, 8 ≤ address → after.heap address = 0) ∧
      ∀ clock, 17 ≤ clock → clock ≤ count →
        natRun rom (program handlerPC (checker ++ rest)) clock natInitial =
          natRun rom checker clock natInitial := by
  obtain ⟨count, bound, active, pc, value, correct, _halt, body, appended⟩ :=
    checker_before_first_halt q full
  have endPC : (natRun (rawIncidenceROM q full) checker count natInitial).pc = 630 := by
    simpa only [checker_length] using pc
  have lower : 17 ≤ count := by
    by_contra notLower
    have early := old_pc_before_seventeen (rawIncidenceROM q full) count (by omega)
    omega
  have same (clock : Nat) (lo : 17 ≤ clock) (hi : clock ≤ count) :
      natRun (rawIncidenceROM q full) (program handlerPC (checker ++ rest)) clock natInitial =
        natRun (rawIncidenceROM q full) checker clock natInitial :=
    checker_patch_eq_after_seventeen (rawIncidenceROM q full) full.length q handlerPC rest count clock
      (raw_header_N q full) (raw_header_q q full) hq (appended rest)
      (fun index hi => (body index hi).2.1) lo hi
  refine ⟨count, lower, bound, ?_⟩
  dsimp only
  rw [same count lower le_rfl]
  refine ⟨rfl, active, endPC, value, correct, ?_, same⟩
  intro address lo
  exact checker_active_heap_frame q full count active address lo

end PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079
