module

public import Structure.PA06_A19Prepare_AllQZero083_Cost
public import Structure.PA06_A19Prepare_AllQCode082
public import Structure.PA06_A19Prepare_EarlyGate079_WordZero
public import Structure.PA06_A19Prepare_Completion060_CanonicalPrefix
public import Structure.PA06_A19Prepare_Access_004

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED complete q0 branch of the ONE actual082 program. The real
8-step gate, real runtime-width/header and real final HALT share the same
original controllerInput/zeroheap run. Static eligibility is proved by082,
not supplied by the original caller. Positiveq remains a separate branch. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQZero083

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PrepareAllQCode082 (program handlerStart handlerLeft oldP)

private theorem header_exit_eq {bits : Nat} (state : WordState bits)
    (pc : state.pc.toNat = 5 * (handlerLeft.length + 60)) :
    state.pc.toNat = 5 * program.length := by
  simpa only [PA06A19PrepareAllQCode082.handlerLeft_length,
    PA06A19PrepareAllQCode082.program_length, PA06A19PrepareAllQCode082.finalEnd] using pc

theorem zero_complete (full : List (Finset (Fin 0))) (used : Finset (Fin 0)) :
    ∃ steps,
      DynamicRunCorrect (PA06A19PreparePreBuild044.allocation 0 full)
        (controllerInput 0 full used) program steps
        (fun _ => BitVec.ofNat (indexWidth 32 full.length 0) 0) ∧
      totalCost (PA06A19PreparePreBuild044.allocation 0 full)
        (controllerInput 0 full used) program steps
        (fun _ => BitVec.ofNat (indexWidth 32 full.length 0) 0) ≤
          costFactor program * (full.length + 1) ∧
      HeapRepresents 0 full 0 ⟨0, used, false⟩
        (packingRun (controllerInput 0 full used) program steps
          (packingInitial (fun _ => BitVec.ofNat (indexWidth 32 full.length 0) 0))).heap := by
  let bits := indexWidth 32 full.length 0
  let H := PA06A19PreparePreBuild044.allocation 0 full
  let rom := controllerInput 0 full used
  let initial := packingInitial (fun _ => BitVec.ofNat bits 0)
  let entered := packingRun rom program 8 initial
  let bodyClock := PA06A19PrepareZeroHeader080.clock full.length
  have certificate := PA06A19PrepareAllQCode082.selected_certificate full.length 0
  have label : handlerStart ≤ program.length := by
    rw [PA06A19PrepareAllQCode082.program_length]
    unfold PA06A19PrepareAllQCode082.finalEnd
    omega
  have gateProgram : PA06A19PrepareEarlyGate079.program (5 * handlerStart) oldP = program := rfl
  have gate := PA06A19PrepareEarlyGate079.zero_word_entry full used handlerStart oldP
    (by rw [gateProgram]; exact label)
    (by rw [gateProgram]; exact certificate.1)
    (by rw [gateProgram]; exact certificate.2)
  rw [gateProgram] at gate
  dsimp only at gate
  have body := PA06A19PrepareZeroHeader080.actual_header full used handlerLeft [] entered
    (by rw [PA06A19PrepareAllQCode082.handlerLeft_length]; exact gate.1)
    gate.2.1
    (by rw [PA06A19PrepareAllQCode082.handler_program_layout]; exact certificate.1)
    (by rw [PA06A19PrepareAllQCode082.handler_program_layout]; exact certificate.2)
  rw [PA06A19PrepareAllQCode082.handler_program_layout] at body
  dsimp only at body
  rcases body with ⟨represents, active, pc, bodyPrefixes⟩
  have bodyRun : packingRun rom program (8 + bodyClock) initial =
      packingRun rom program bodyClock entered :=
    PA06A19PrepareRawHeader039Body.wordRun_add rom program 8 bodyClock initial
  have fetched := PA06A19PrepareCompletion060Canonical.fetched_add H rom program initial 8 bodyClock
    gate.2.2.1 (by
      intro count bound
      exact bodyPrefixes count bound)
  have endPC : (packingRun rom program (8 + bodyClock) initial).pc.toNat = 5 * program.length := by
    rw [bodyRun]
    exact header_exit_eq _ pc
  have endActive : (packingRun rom program (8 + bodyClock) initial).halted = false := by
    rw [bodyRun]
    exact active
  have completed := PA06A19PrepareCompletion060Canonical.fetched_halt H rom program initial (8 + bodyClock)
    fetched certificate.1 certificate.2 endPC endActive
  have represented : HeapRepresents 0 full 0 ⟨0, used, false⟩
      (packingRun rom program (8 + bodyClock + 1) initial).heap := by
    rw [completed.2.1, bodyRun]
    exact represents
  have footprint := PA06A19PrepareEarlyGate079.zero_original_footprint_fits full used program
    PA06A19PrepareAllQCode082.encoded_length_le29
  have steps := total_steps_le full.length
  have cost := whole_cost_le full used program (8 + bodyClock + 1) steps
  refine ⟨8 + bodyClock + 1, ?_, cost, represented⟩
  exact ⟨certificate.1, PA06A19PrepareAccess004.controllerInput_wordsFit 32 0 full used (by decide),
    footprint, completed.2.2.1, completed.2.2.2⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQZero083
